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
% DateTime   : Thu Dec  3 12:22:58 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1031)

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

fof(f37,plain,(
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

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,sK4,X3)),k2_tmap_1(X0,X1,sK4,X2))
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,k2_tmap_1(X0,X1,X4,sK3)),k2_tmap_1(X0,X1,X4,X2))
            & m1_pre_topc(X2,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
                ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,sK2))
                & m1_pre_topc(sK2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,k2_tmap_1(X0,sK1,X4,X3)),k2_tmap_1(X0,sK1,X4,X2))
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

fof(f23,plain,
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
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,k2_tmap_1(sK0,X1,X4,X3)),k2_tmap_1(sK0,X1,X4,X2))
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

fof(f28,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f27,f26,f25,f24,f23])).

fof(f47,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f32,plain,(
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

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f31,plain,(
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

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f36,plain,(
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

fof(f35,plain,(
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
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f30])).

fof(f33,plain,(
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

fof(f34,plain,(
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

fof(f52,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8,plain,
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
    | v2_struct_0(X5)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_267,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,k2_tmap_1(X2_47,X1_47,X1_48,X0_47))
    | r2_funct_2(u1_struct_0(X3_47),u1_struct_0(X1_47),k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),k2_tmap_1(X2_47,X1_47,X1_48,X3_47))
    | ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
    | ~ v1_funct_2(X1_48,u1_struct_0(X2_47),u1_struct_0(X1_47))
    | ~ m1_pre_topc(X3_47,X2_47)
    | ~ m1_pre_topc(X3_47,X0_47)
    | ~ m1_pre_topc(X0_47,X2_47)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_47),u1_struct_0(X1_47))))
    | v2_struct_0(X3_47)
    | v2_struct_0(X1_47)
    | v2_struct_0(X0_47)
    | v2_struct_0(X2_47)
    | ~ v2_pre_topc(X1_47)
    | ~ v2_pre_topc(X2_47)
    | ~ l1_pre_topc(X1_47)
    | ~ l1_pre_topc(X2_47)
    | ~ v1_funct_1(X1_48)
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1133,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_47),u1_struct_0(sK1),X0_48,k2_tmap_1(X1_47,sK1,X1_48,X0_47))
    | r2_funct_2(u1_struct_0(X2_47),u1_struct_0(sK1),k3_tmap_1(X1_47,sK1,X0_47,X2_47,X0_48),k2_tmap_1(X1_47,sK1,X1_48,X2_47))
    | ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(sK1))
    | ~ v1_funct_2(X1_48,u1_struct_0(X1_47),u1_struct_0(sK1))
    | ~ m1_pre_topc(X2_47,X0_47)
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ m1_pre_topc(X2_47,X1_47)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(sK1))))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_47),u1_struct_0(sK1))))
    | v2_struct_0(X1_47)
    | v2_struct_0(X0_47)
    | v2_struct_0(X2_47)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X1_47)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_47)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X1_48)
    | ~ v1_funct_1(X0_48) ),
    inference(instantiation,[status(thm)],[c_267])).

cnf(c_1275,plain,
    ( r2_funct_2(u1_struct_0(X0_47),u1_struct_0(sK1),k3_tmap_1(X1_47,sK1,X2_47,X0_47,k2_tmap_1(X1_47,sK1,X0_48,X2_47)),k2_tmap_1(X1_47,sK1,X0_48,X0_47))
    | ~ r2_funct_2(u1_struct_0(X2_47),u1_struct_0(sK1),k2_tmap_1(X1_47,sK1,X0_48,X2_47),k2_tmap_1(X1_47,sK1,X0_48,X2_47))
    | ~ v1_funct_2(X0_48,u1_struct_0(X1_47),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(X1_47,sK1,X0_48,X2_47),u1_struct_0(X2_47),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_47,X2_47)
    | ~ m1_pre_topc(X2_47,X1_47)
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_47),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(X1_47,sK1,X0_48,X2_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_47),u1_struct_0(sK1))))
    | v2_struct_0(X1_47)
    | v2_struct_0(X2_47)
    | v2_struct_0(X0_47)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X1_47)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_47)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(k2_tmap_1(X1_47,sK1,X0_48,X2_47)) ),
    inference(instantiation,[status(thm)],[c_1133])).

cnf(c_8485,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1275])).

cnf(c_14,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_261,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_711,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_264,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_708,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_264])).

cnf(c_3,plain,
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
    inference(cnf_transformation,[],[f32])).

cnf(c_272,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
    | ~ m1_pre_topc(X0_47,X2_47)
    | ~ m1_pre_topc(X3_47,X2_47)
    | ~ m1_pre_topc(X3_47,X0_47)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
    | v2_struct_0(X2_47)
    | v2_struct_0(X1_47)
    | ~ v2_pre_topc(X1_47)
    | ~ v2_pre_topc(X2_47)
    | ~ l1_pre_topc(X1_47)
    | ~ l1_pre_topc(X2_47)
    | ~ v1_funct_1(X0_48)
    | k2_partfun1(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,u1_struct_0(X3_47)) = k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_700,plain,
    ( k2_partfun1(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,u1_struct_0(X2_47)) = k3_tmap_1(X3_47,X1_47,X0_47,X2_47,X0_48)
    | v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
    | m1_pre_topc(X2_47,X0_47) != iProver_top
    | m1_pre_topc(X0_47,X3_47) != iProver_top
    | m1_pre_topc(X2_47,X3_47) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X3_47) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | v2_pre_topc(X3_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X3_47) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_1961,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | m1_pre_topc(X0_47,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_708,c_700])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_27,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_28,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_29,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_34,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_35,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2328,plain,
    ( v2_pre_topc(X1_47) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | m1_pre_topc(X0_47,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1961,c_27,c_28,c_29,c_34,c_35,c_36,c_1031])).

cnf(c_2329,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | m1_pre_topc(X0_47,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_2328])).

cnf(c_2342,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_711,c_2329])).

cnf(c_2,plain,
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
    inference(cnf_transformation,[],[f31])).

cnf(c_273,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
    | ~ m1_pre_topc(X2_47,X0_47)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
    | v2_struct_0(X1_47)
    | v2_struct_0(X0_47)
    | ~ v2_pre_topc(X1_47)
    | ~ v2_pre_topc(X0_47)
    | ~ l1_pre_topc(X1_47)
    | ~ l1_pre_topc(X0_47)
    | ~ v1_funct_1(X0_48)
    | k2_partfun1(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,u1_struct_0(X2_47)) = k2_tmap_1(X0_47,X1_47,X0_48,X2_47) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_699,plain,
    ( k2_partfun1(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,u1_struct_0(X2_47)) = k2_tmap_1(X0_47,X1_47,X0_48,X2_47)
    | v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
    | m1_pre_topc(X2_47,X0_47) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | v2_pre_topc(X0_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_1604,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k2_tmap_1(sK0,sK1,sK4,X0_47)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_47,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_708,c_699])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_24,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_25,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_26,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2034,plain,
    ( m1_pre_topc(X0_47,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k2_tmap_1(sK0,sK1,sK4,X0_47) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1604,c_24,c_25,c_26,c_27,c_28,c_29,c_34,c_35])).

cnf(c_2035,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k2_tmap_1(sK0,sK1,sK4,X0_47)
    | m1_pre_topc(X0_47,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2034])).

cnf(c_2042,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_711,c_2035])).

cnf(c_2376,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2342,c_2042])).

cnf(c_33,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_42,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_44,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_3511,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2376,c_24,c_25,c_26,c_33,c_44])).

cnf(c_4,plain,
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
    inference(cnf_transformation,[],[f35])).

cnf(c_271,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
    | ~ m1_pre_topc(X0_47,X2_47)
    | ~ m1_pre_topc(X3_47,X2_47)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
    | m1_subset_1(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_47),u1_struct_0(X1_47))))
    | v2_struct_0(X2_47)
    | v2_struct_0(X1_47)
    | ~ v2_pre_topc(X1_47)
    | ~ v2_pre_topc(X2_47)
    | ~ l1_pre_topc(X1_47)
    | ~ l1_pre_topc(X2_47)
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_701,plain,
    ( v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
    | m1_pre_topc(X0_47,X2_47) != iProver_top
    | m1_pre_topc(X3_47,X2_47) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_47),u1_struct_0(X1_47)))) = iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X2_47) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | v2_pre_topc(X2_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X2_47) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_271])).

cnf(c_3514,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3511,c_701])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5021,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3514,c_24,c_25,c_26,c_27,c_28,c_29,c_33,c_34,c_35,c_36,c_44])).

cnf(c_0,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_275,plain,
    ( r2_funct_2(X0_49,X1_49,X0_48,X0_48)
    | ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_697,plain,
    ( r2_funct_2(X0_49,X1_49,X0_48,X0_48) = iProver_top
    | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_275])).

cnf(c_5030,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5021,c_697])).

cnf(c_5129,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5030])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f33])).

cnf(c_269,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
    | ~ m1_pre_topc(X0_47,X2_47)
    | ~ m1_pre_topc(X3_47,X2_47)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
    | v2_struct_0(X2_47)
    | v2_struct_0(X1_47)
    | ~ v2_pre_topc(X1_47)
    | ~ v2_pre_topc(X2_47)
    | ~ l1_pre_topc(X1_47)
    | ~ l1_pre_topc(X2_47)
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_703,plain,
    ( v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
    | m1_pre_topc(X0_47,X2_47) != iProver_top
    | m1_pre_topc(X3_47,X2_47) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X2_47) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | v2_pre_topc(X2_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X2_47) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_1621,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | m1_pre_topc(sK0,X1_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_708,c_703])).

cnf(c_1006,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ m1_pre_topc(sK0,X1_47)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(X1_47)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X1_47)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_47)
    | ~ l1_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_1007,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | m1_pre_topc(sK0,X1_47) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1006])).

cnf(c_2315,plain,
    ( v1_funct_1(k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | m1_pre_topc(sK0,X1_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1621,c_27,c_28,c_29,c_34,c_35])).

cnf(c_2316,plain,
    ( m1_pre_topc(X0_47,X1_47) != iProver_top
    | m1_pre_topc(sK0,X1_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2315])).

cnf(c_3516,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3511,c_2316])).

cnf(c_3579,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3516])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f34])).

cnf(c_270,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
    | v1_funct_2(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),u1_struct_0(X3_47),u1_struct_0(X1_47))
    | ~ m1_pre_topc(X3_47,X2_47)
    | ~ m1_pre_topc(X0_47,X2_47)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
    | v2_struct_0(X1_47)
    | v2_struct_0(X2_47)
    | ~ v2_pre_topc(X1_47)
    | ~ v2_pre_topc(X2_47)
    | ~ l1_pre_topc(X1_47)
    | ~ l1_pre_topc(X2_47)
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_702,plain,
    ( v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),u1_struct_0(X3_47),u1_struct_0(X1_47)) = iProver_top
    | m1_pre_topc(X0_47,X2_47) != iProver_top
    | m1_pre_topc(X3_47,X2_47) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X2_47) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | v2_pre_topc(X2_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X2_47) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_3515,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3511,c_702])).

cnf(c_3578,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3515])).

cnf(c_3577,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3514])).

cnf(c_43,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_9,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_10,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_15,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8485,c_5129,c_3579,c_3578,c_3577,c_43,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.24/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/0.98  
% 3.24/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.24/0.98  
% 3.24/0.98  ------  iProver source info
% 3.24/0.98  
% 3.24/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.24/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.24/0.98  git: non_committed_changes: false
% 3.24/0.98  git: last_make_outside_of_git: false
% 3.24/0.98  
% 3.24/0.98  ------ 
% 3.24/0.98  
% 3.24/0.98  ------ Input Options
% 3.24/0.98  
% 3.24/0.98  --out_options                           all
% 3.24/0.98  --tptp_safe_out                         true
% 3.24/0.98  --problem_path                          ""
% 3.24/0.98  --include_path                          ""
% 3.24/0.98  --clausifier                            res/vclausify_rel
% 3.24/0.98  --clausifier_options                    --mode clausify
% 3.24/0.98  --stdin                                 false
% 3.24/0.98  --stats_out                             all
% 3.24/0.98  
% 3.24/0.98  ------ General Options
% 3.24/0.98  
% 3.24/0.98  --fof                                   false
% 3.24/0.98  --time_out_real                         305.
% 3.24/0.98  --time_out_virtual                      -1.
% 3.24/0.98  --symbol_type_check                     false
% 3.24/0.98  --clausify_out                          false
% 3.24/0.98  --sig_cnt_out                           false
% 3.24/0.98  --trig_cnt_out                          false
% 3.24/0.98  --trig_cnt_out_tolerance                1.
% 3.24/0.98  --trig_cnt_out_sk_spl                   false
% 3.24/0.98  --abstr_cl_out                          false
% 3.24/0.98  
% 3.24/0.98  ------ Global Options
% 3.24/0.98  
% 3.24/0.98  --schedule                              default
% 3.24/0.98  --add_important_lit                     false
% 3.24/0.98  --prop_solver_per_cl                    1000
% 3.24/0.98  --min_unsat_core                        false
% 3.24/0.98  --soft_assumptions                      false
% 3.24/0.98  --soft_lemma_size                       3
% 3.24/0.98  --prop_impl_unit_size                   0
% 3.24/0.98  --prop_impl_unit                        []
% 3.24/0.98  --share_sel_clauses                     true
% 3.24/0.98  --reset_solvers                         false
% 3.24/0.98  --bc_imp_inh                            [conj_cone]
% 3.24/0.98  --conj_cone_tolerance                   3.
% 3.24/0.98  --extra_neg_conj                        none
% 3.24/0.98  --large_theory_mode                     true
% 3.24/0.98  --prolific_symb_bound                   200
% 3.24/0.98  --lt_threshold                          2000
% 3.24/0.98  --clause_weak_htbl                      true
% 3.24/0.98  --gc_record_bc_elim                     false
% 3.24/0.98  
% 3.24/0.98  ------ Preprocessing Options
% 3.24/0.98  
% 3.24/0.98  --preprocessing_flag                    true
% 3.24/0.98  --time_out_prep_mult                    0.1
% 3.24/0.98  --splitting_mode                        input
% 3.24/0.98  --splitting_grd                         true
% 3.24/0.98  --splitting_cvd                         false
% 3.24/0.98  --splitting_cvd_svl                     false
% 3.24/0.98  --splitting_nvd                         32
% 3.24/0.98  --sub_typing                            true
% 3.24/0.98  --prep_gs_sim                           true
% 3.24/0.98  --prep_unflatten                        true
% 3.24/0.98  --prep_res_sim                          true
% 3.24/0.98  --prep_upred                            true
% 3.24/0.98  --prep_sem_filter                       exhaustive
% 3.24/0.98  --prep_sem_filter_out                   false
% 3.24/0.98  --pred_elim                             true
% 3.24/0.98  --res_sim_input                         true
% 3.24/0.98  --eq_ax_congr_red                       true
% 3.24/0.98  --pure_diseq_elim                       true
% 3.24/0.98  --brand_transform                       false
% 3.24/0.98  --non_eq_to_eq                          false
% 3.24/0.98  --prep_def_merge                        true
% 3.24/0.98  --prep_def_merge_prop_impl              false
% 3.24/0.98  --prep_def_merge_mbd                    true
% 3.24/0.98  --prep_def_merge_tr_red                 false
% 3.24/0.98  --prep_def_merge_tr_cl                  false
% 3.24/0.98  --smt_preprocessing                     true
% 3.24/0.98  --smt_ac_axioms                         fast
% 3.24/0.98  --preprocessed_out                      false
% 3.24/0.98  --preprocessed_stats                    false
% 3.24/0.98  
% 3.24/0.98  ------ Abstraction refinement Options
% 3.24/0.98  
% 3.24/0.98  --abstr_ref                             []
% 3.24/0.98  --abstr_ref_prep                        false
% 3.24/0.98  --abstr_ref_until_sat                   false
% 3.24/0.98  --abstr_ref_sig_restrict                funpre
% 3.24/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/0.98  --abstr_ref_under                       []
% 3.24/0.98  
% 3.24/0.98  ------ SAT Options
% 3.24/0.98  
% 3.24/0.98  --sat_mode                              false
% 3.24/0.98  --sat_fm_restart_options                ""
% 3.24/0.98  --sat_gr_def                            false
% 3.24/0.98  --sat_epr_types                         true
% 3.24/0.98  --sat_non_cyclic_types                  false
% 3.24/0.98  --sat_finite_models                     false
% 3.24/0.98  --sat_fm_lemmas                         false
% 3.24/0.98  --sat_fm_prep                           false
% 3.24/0.99  --sat_fm_uc_incr                        true
% 3.24/0.99  --sat_out_model                         small
% 3.24/0.99  --sat_out_clauses                       false
% 3.24/0.99  
% 3.24/0.99  ------ QBF Options
% 3.24/0.99  
% 3.24/0.99  --qbf_mode                              false
% 3.24/0.99  --qbf_elim_univ                         false
% 3.24/0.99  --qbf_dom_inst                          none
% 3.24/0.99  --qbf_dom_pre_inst                      false
% 3.24/0.99  --qbf_sk_in                             false
% 3.24/0.99  --qbf_pred_elim                         true
% 3.24/0.99  --qbf_split                             512
% 3.24/0.99  
% 3.24/0.99  ------ BMC1 Options
% 3.24/0.99  
% 3.24/0.99  --bmc1_incremental                      false
% 3.24/0.99  --bmc1_axioms                           reachable_all
% 3.24/0.99  --bmc1_min_bound                        0
% 3.24/0.99  --bmc1_max_bound                        -1
% 3.24/0.99  --bmc1_max_bound_default                -1
% 3.24/0.99  --bmc1_symbol_reachability              true
% 3.24/0.99  --bmc1_property_lemmas                  false
% 3.24/0.99  --bmc1_k_induction                      false
% 3.24/0.99  --bmc1_non_equiv_states                 false
% 3.24/0.99  --bmc1_deadlock                         false
% 3.24/0.99  --bmc1_ucm                              false
% 3.24/0.99  --bmc1_add_unsat_core                   none
% 3.24/0.99  --bmc1_unsat_core_children              false
% 3.24/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/0.99  --bmc1_out_stat                         full
% 3.24/0.99  --bmc1_ground_init                      false
% 3.24/0.99  --bmc1_pre_inst_next_state              false
% 3.24/0.99  --bmc1_pre_inst_state                   false
% 3.24/0.99  --bmc1_pre_inst_reach_state             false
% 3.24/0.99  --bmc1_out_unsat_core                   false
% 3.24/0.99  --bmc1_aig_witness_out                  false
% 3.24/0.99  --bmc1_verbose                          false
% 3.24/0.99  --bmc1_dump_clauses_tptp                false
% 3.24/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.24/0.99  --bmc1_dump_file                        -
% 3.24/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.24/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.24/0.99  --bmc1_ucm_extend_mode                  1
% 3.24/0.99  --bmc1_ucm_init_mode                    2
% 3.24/0.99  --bmc1_ucm_cone_mode                    none
% 3.24/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.24/0.99  --bmc1_ucm_relax_model                  4
% 3.24/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.24/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/0.99  --bmc1_ucm_layered_model                none
% 3.24/0.99  --bmc1_ucm_max_lemma_size               10
% 3.24/0.99  
% 3.24/0.99  ------ AIG Options
% 3.24/0.99  
% 3.24/0.99  --aig_mode                              false
% 3.24/0.99  
% 3.24/0.99  ------ Instantiation Options
% 3.24/0.99  
% 3.24/0.99  --instantiation_flag                    true
% 3.24/0.99  --inst_sos_flag                         false
% 3.24/0.99  --inst_sos_phase                        true
% 3.24/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/0.99  --inst_lit_sel_side                     num_symb
% 3.24/0.99  --inst_solver_per_active                1400
% 3.24/0.99  --inst_solver_calls_frac                1.
% 3.24/0.99  --inst_passive_queue_type               priority_queues
% 3.24/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/0.99  --inst_passive_queues_freq              [25;2]
% 3.24/0.99  --inst_dismatching                      true
% 3.24/0.99  --inst_eager_unprocessed_to_passive     true
% 3.24/0.99  --inst_prop_sim_given                   true
% 3.24/0.99  --inst_prop_sim_new                     false
% 3.24/0.99  --inst_subs_new                         false
% 3.24/0.99  --inst_eq_res_simp                      false
% 3.24/0.99  --inst_subs_given                       false
% 3.24/0.99  --inst_orphan_elimination               true
% 3.24/0.99  --inst_learning_loop_flag               true
% 3.24/0.99  --inst_learning_start                   3000
% 3.24/0.99  --inst_learning_factor                  2
% 3.24/0.99  --inst_start_prop_sim_after_learn       3
% 3.24/0.99  --inst_sel_renew                        solver
% 3.24/0.99  --inst_lit_activity_flag                true
% 3.24/0.99  --inst_restr_to_given                   false
% 3.24/0.99  --inst_activity_threshold               500
% 3.24/0.99  --inst_out_proof                        true
% 3.24/0.99  
% 3.24/0.99  ------ Resolution Options
% 3.24/0.99  
% 3.24/0.99  --resolution_flag                       true
% 3.24/0.99  --res_lit_sel                           adaptive
% 3.24/0.99  --res_lit_sel_side                      none
% 3.24/0.99  --res_ordering                          kbo
% 3.24/0.99  --res_to_prop_solver                    active
% 3.24/0.99  --res_prop_simpl_new                    false
% 3.24/0.99  --res_prop_simpl_given                  true
% 3.24/0.99  --res_passive_queue_type                priority_queues
% 3.24/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/0.99  --res_passive_queues_freq               [15;5]
% 3.24/0.99  --res_forward_subs                      full
% 3.24/0.99  --res_backward_subs                     full
% 3.24/0.99  --res_forward_subs_resolution           true
% 3.24/0.99  --res_backward_subs_resolution          true
% 3.24/0.99  --res_orphan_elimination                true
% 3.24/0.99  --res_time_limit                        2.
% 3.24/0.99  --res_out_proof                         true
% 3.24/0.99  
% 3.24/0.99  ------ Superposition Options
% 3.24/0.99  
% 3.24/0.99  --superposition_flag                    true
% 3.24/0.99  --sup_passive_queue_type                priority_queues
% 3.24/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.24/0.99  --demod_completeness_check              fast
% 3.24/0.99  --demod_use_ground                      true
% 3.24/0.99  --sup_to_prop_solver                    passive
% 3.24/0.99  --sup_prop_simpl_new                    true
% 3.24/0.99  --sup_prop_simpl_given                  true
% 3.24/0.99  --sup_fun_splitting                     false
% 3.24/0.99  --sup_smt_interval                      50000
% 3.24/0.99  
% 3.24/0.99  ------ Superposition Simplification Setup
% 3.24/0.99  
% 3.24/0.99  --sup_indices_passive                   []
% 3.24/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.99  --sup_full_bw                           [BwDemod]
% 3.24/0.99  --sup_immed_triv                        [TrivRules]
% 3.24/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.99  --sup_immed_bw_main                     []
% 3.24/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/0.99  
% 3.24/0.99  ------ Combination Options
% 3.24/0.99  
% 3.24/0.99  --comb_res_mult                         3
% 3.24/0.99  --comb_sup_mult                         2
% 3.24/0.99  --comb_inst_mult                        10
% 3.24/0.99  
% 3.24/0.99  ------ Debug Options
% 3.24/0.99  
% 3.24/0.99  --dbg_backtrace                         false
% 3.24/0.99  --dbg_dump_prop_clauses                 false
% 3.24/0.99  --dbg_dump_prop_clauses_file            -
% 3.24/0.99  --dbg_out_stat                          false
% 3.24/0.99  ------ Parsing...
% 3.24/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.24/0.99  
% 3.24/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.24/0.99  
% 3.24/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.24/0.99  
% 3.24/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.24/0.99  ------ Proving...
% 3.24/0.99  ------ Problem Properties 
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  clauses                                 24
% 3.24/0.99  conjectures                             15
% 3.24/0.99  EPR                                     13
% 3.24/0.99  Horn                                    18
% 3.24/0.99  unary                                   15
% 3.24/0.99  binary                                  1
% 3.24/0.99  lits                                    108
% 3.24/0.99  lits eq                                 3
% 3.24/0.99  fd_pure                                 0
% 3.24/0.99  fd_pseudo                               0
% 3.24/0.99  fd_cond                                 0
% 3.24/0.99  fd_pseudo_cond                          1
% 3.24/0.99  AC symbols                              0
% 3.24/0.99  
% 3.24/0.99  ------ Schedule dynamic 5 is on 
% 3.24/0.99  
% 3.24/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  ------ 
% 3.24/0.99  Current options:
% 3.24/0.99  ------ 
% 3.24/0.99  
% 3.24/0.99  ------ Input Options
% 3.24/0.99  
% 3.24/0.99  --out_options                           all
% 3.24/0.99  --tptp_safe_out                         true
% 3.24/0.99  --problem_path                          ""
% 3.24/0.99  --include_path                          ""
% 3.24/0.99  --clausifier                            res/vclausify_rel
% 3.24/0.99  --clausifier_options                    --mode clausify
% 3.24/0.99  --stdin                                 false
% 3.24/0.99  --stats_out                             all
% 3.24/0.99  
% 3.24/0.99  ------ General Options
% 3.24/0.99  
% 3.24/0.99  --fof                                   false
% 3.24/0.99  --time_out_real                         305.
% 3.24/0.99  --time_out_virtual                      -1.
% 3.24/0.99  --symbol_type_check                     false
% 3.24/0.99  --clausify_out                          false
% 3.24/0.99  --sig_cnt_out                           false
% 3.24/0.99  --trig_cnt_out                          false
% 3.24/0.99  --trig_cnt_out_tolerance                1.
% 3.24/0.99  --trig_cnt_out_sk_spl                   false
% 3.24/0.99  --abstr_cl_out                          false
% 3.24/0.99  
% 3.24/0.99  ------ Global Options
% 3.24/0.99  
% 3.24/0.99  --schedule                              default
% 3.24/0.99  --add_important_lit                     false
% 3.24/0.99  --prop_solver_per_cl                    1000
% 3.24/0.99  --min_unsat_core                        false
% 3.24/0.99  --soft_assumptions                      false
% 3.24/0.99  --soft_lemma_size                       3
% 3.24/0.99  --prop_impl_unit_size                   0
% 3.24/0.99  --prop_impl_unit                        []
% 3.24/0.99  --share_sel_clauses                     true
% 3.24/0.99  --reset_solvers                         false
% 3.24/0.99  --bc_imp_inh                            [conj_cone]
% 3.24/0.99  --conj_cone_tolerance                   3.
% 3.24/0.99  --extra_neg_conj                        none
% 3.24/0.99  --large_theory_mode                     true
% 3.24/0.99  --prolific_symb_bound                   200
% 3.24/0.99  --lt_threshold                          2000
% 3.24/0.99  --clause_weak_htbl                      true
% 3.24/0.99  --gc_record_bc_elim                     false
% 3.24/0.99  
% 3.24/0.99  ------ Preprocessing Options
% 3.24/0.99  
% 3.24/0.99  --preprocessing_flag                    true
% 3.24/0.99  --time_out_prep_mult                    0.1
% 3.24/0.99  --splitting_mode                        input
% 3.24/0.99  --splitting_grd                         true
% 3.24/0.99  --splitting_cvd                         false
% 3.24/0.99  --splitting_cvd_svl                     false
% 3.24/0.99  --splitting_nvd                         32
% 3.24/0.99  --sub_typing                            true
% 3.24/0.99  --prep_gs_sim                           true
% 3.24/0.99  --prep_unflatten                        true
% 3.24/0.99  --prep_res_sim                          true
% 3.24/0.99  --prep_upred                            true
% 3.24/0.99  --prep_sem_filter                       exhaustive
% 3.24/0.99  --prep_sem_filter_out                   false
% 3.24/0.99  --pred_elim                             true
% 3.24/0.99  --res_sim_input                         true
% 3.24/0.99  --eq_ax_congr_red                       true
% 3.24/0.99  --pure_diseq_elim                       true
% 3.24/0.99  --brand_transform                       false
% 3.24/0.99  --non_eq_to_eq                          false
% 3.24/0.99  --prep_def_merge                        true
% 3.24/0.99  --prep_def_merge_prop_impl              false
% 3.24/0.99  --prep_def_merge_mbd                    true
% 3.24/0.99  --prep_def_merge_tr_red                 false
% 3.24/0.99  --prep_def_merge_tr_cl                  false
% 3.24/0.99  --smt_preprocessing                     true
% 3.24/0.99  --smt_ac_axioms                         fast
% 3.24/0.99  --preprocessed_out                      false
% 3.24/0.99  --preprocessed_stats                    false
% 3.24/0.99  
% 3.24/0.99  ------ Abstraction refinement Options
% 3.24/0.99  
% 3.24/0.99  --abstr_ref                             []
% 3.24/0.99  --abstr_ref_prep                        false
% 3.24/0.99  --abstr_ref_until_sat                   false
% 3.24/0.99  --abstr_ref_sig_restrict                funpre
% 3.24/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/0.99  --abstr_ref_under                       []
% 3.24/0.99  
% 3.24/0.99  ------ SAT Options
% 3.24/0.99  
% 3.24/0.99  --sat_mode                              false
% 3.24/0.99  --sat_fm_restart_options                ""
% 3.24/0.99  --sat_gr_def                            false
% 3.24/0.99  --sat_epr_types                         true
% 3.24/0.99  --sat_non_cyclic_types                  false
% 3.24/0.99  --sat_finite_models                     false
% 3.24/0.99  --sat_fm_lemmas                         false
% 3.24/0.99  --sat_fm_prep                           false
% 3.24/0.99  --sat_fm_uc_incr                        true
% 3.24/0.99  --sat_out_model                         small
% 3.24/0.99  --sat_out_clauses                       false
% 3.24/0.99  
% 3.24/0.99  ------ QBF Options
% 3.24/0.99  
% 3.24/0.99  --qbf_mode                              false
% 3.24/0.99  --qbf_elim_univ                         false
% 3.24/0.99  --qbf_dom_inst                          none
% 3.24/0.99  --qbf_dom_pre_inst                      false
% 3.24/0.99  --qbf_sk_in                             false
% 3.24/0.99  --qbf_pred_elim                         true
% 3.24/0.99  --qbf_split                             512
% 3.24/0.99  
% 3.24/0.99  ------ BMC1 Options
% 3.24/0.99  
% 3.24/0.99  --bmc1_incremental                      false
% 3.24/0.99  --bmc1_axioms                           reachable_all
% 3.24/0.99  --bmc1_min_bound                        0
% 3.24/0.99  --bmc1_max_bound                        -1
% 3.24/0.99  --bmc1_max_bound_default                -1
% 3.24/0.99  --bmc1_symbol_reachability              true
% 3.24/0.99  --bmc1_property_lemmas                  false
% 3.24/0.99  --bmc1_k_induction                      false
% 3.24/0.99  --bmc1_non_equiv_states                 false
% 3.24/0.99  --bmc1_deadlock                         false
% 3.24/0.99  --bmc1_ucm                              false
% 3.24/0.99  --bmc1_add_unsat_core                   none
% 3.24/0.99  --bmc1_unsat_core_children              false
% 3.24/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/0.99  --bmc1_out_stat                         full
% 3.24/0.99  --bmc1_ground_init                      false
% 3.24/0.99  --bmc1_pre_inst_next_state              false
% 3.24/0.99  --bmc1_pre_inst_state                   false
% 3.24/0.99  --bmc1_pre_inst_reach_state             false
% 3.24/0.99  --bmc1_out_unsat_core                   false
% 3.24/0.99  --bmc1_aig_witness_out                  false
% 3.24/0.99  --bmc1_verbose                          false
% 3.24/0.99  --bmc1_dump_clauses_tptp                false
% 3.24/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.24/0.99  --bmc1_dump_file                        -
% 3.24/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.24/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.24/0.99  --bmc1_ucm_extend_mode                  1
% 3.24/0.99  --bmc1_ucm_init_mode                    2
% 3.24/0.99  --bmc1_ucm_cone_mode                    none
% 3.24/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.24/0.99  --bmc1_ucm_relax_model                  4
% 3.24/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.24/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/0.99  --bmc1_ucm_layered_model                none
% 3.24/0.99  --bmc1_ucm_max_lemma_size               10
% 3.24/0.99  
% 3.24/0.99  ------ AIG Options
% 3.24/0.99  
% 3.24/0.99  --aig_mode                              false
% 3.24/0.99  
% 3.24/0.99  ------ Instantiation Options
% 3.24/0.99  
% 3.24/0.99  --instantiation_flag                    true
% 3.24/0.99  --inst_sos_flag                         false
% 3.24/0.99  --inst_sos_phase                        true
% 3.24/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/0.99  --inst_lit_sel_side                     none
% 3.24/0.99  --inst_solver_per_active                1400
% 3.24/0.99  --inst_solver_calls_frac                1.
% 3.24/0.99  --inst_passive_queue_type               priority_queues
% 3.24/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/0.99  --inst_passive_queues_freq              [25;2]
% 3.24/0.99  --inst_dismatching                      true
% 3.24/0.99  --inst_eager_unprocessed_to_passive     true
% 3.24/0.99  --inst_prop_sim_given                   true
% 3.24/0.99  --inst_prop_sim_new                     false
% 3.24/0.99  --inst_subs_new                         false
% 3.24/0.99  --inst_eq_res_simp                      false
% 3.24/0.99  --inst_subs_given                       false
% 3.24/0.99  --inst_orphan_elimination               true
% 3.24/0.99  --inst_learning_loop_flag               true
% 3.24/0.99  --inst_learning_start                   3000
% 3.24/0.99  --inst_learning_factor                  2
% 3.24/0.99  --inst_start_prop_sim_after_learn       3
% 3.24/0.99  --inst_sel_renew                        solver
% 3.24/0.99  --inst_lit_activity_flag                true
% 3.24/0.99  --inst_restr_to_given                   false
% 3.24/0.99  --inst_activity_threshold               500
% 3.24/0.99  --inst_out_proof                        true
% 3.24/0.99  
% 3.24/0.99  ------ Resolution Options
% 3.24/0.99  
% 3.24/0.99  --resolution_flag                       false
% 3.24/0.99  --res_lit_sel                           adaptive
% 3.24/0.99  --res_lit_sel_side                      none
% 3.24/0.99  --res_ordering                          kbo
% 3.24/0.99  --res_to_prop_solver                    active
% 3.24/0.99  --res_prop_simpl_new                    false
% 3.24/0.99  --res_prop_simpl_given                  true
% 3.24/0.99  --res_passive_queue_type                priority_queues
% 3.24/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/0.99  --res_passive_queues_freq               [15;5]
% 3.24/0.99  --res_forward_subs                      full
% 3.24/0.99  --res_backward_subs                     full
% 3.24/0.99  --res_forward_subs_resolution           true
% 3.24/0.99  --res_backward_subs_resolution          true
% 3.24/0.99  --res_orphan_elimination                true
% 3.24/0.99  --res_time_limit                        2.
% 3.24/0.99  --res_out_proof                         true
% 3.24/0.99  
% 3.24/0.99  ------ Superposition Options
% 3.24/0.99  
% 3.24/0.99  --superposition_flag                    true
% 3.24/0.99  --sup_passive_queue_type                priority_queues
% 3.24/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.24/0.99  --demod_completeness_check              fast
% 3.24/0.99  --demod_use_ground                      true
% 3.24/0.99  --sup_to_prop_solver                    passive
% 3.24/0.99  --sup_prop_simpl_new                    true
% 3.24/0.99  --sup_prop_simpl_given                  true
% 3.24/0.99  --sup_fun_splitting                     false
% 3.24/0.99  --sup_smt_interval                      50000
% 3.24/0.99  
% 3.24/0.99  ------ Superposition Simplification Setup
% 3.24/0.99  
% 3.24/0.99  --sup_indices_passive                   []
% 3.24/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.99  --sup_full_bw                           [BwDemod]
% 3.24/0.99  --sup_immed_triv                        [TrivRules]
% 3.24/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.99  --sup_immed_bw_main                     []
% 3.24/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/0.99  
% 3.24/0.99  ------ Combination Options
% 3.24/0.99  
% 3.24/0.99  --comb_res_mult                         3
% 3.24/0.99  --comb_sup_mult                         2
% 3.24/0.99  --comb_inst_mult                        10
% 3.24/0.99  
% 3.24/0.99  ------ Debug Options
% 3.24/0.99  
% 3.24/0.99  --dbg_backtrace                         false
% 3.24/0.99  --dbg_dump_prop_clauses                 false
% 3.24/0.99  --dbg_dump_prop_clauses_file            -
% 3.24/0.99  --dbg_out_stat                          false
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  ------ Proving...
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  % SZS status Theorem for theBenchmark.p
% 3.24/0.99  
% 3.24/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.24/0.99  
% 3.24/0.99  fof(f6,axiom,(
% 3.24/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_pre_topc(X3,X2) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))) => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f18,plain,(
% 3.24/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | (~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.24/0.99    inference(ennf_transformation,[],[f6])).
% 3.24/0.99  
% 3.24/0.99  fof(f19,plain,(
% 3.24/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.24/0.99    inference(flattening,[],[f18])).
% 3.24/0.99  
% 3.24/0.99  fof(f37,plain,(
% 3.24/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.24/0.99    inference(cnf_transformation,[],[f19])).
% 3.24/0.99  
% 3.24/0.99  fof(f7,conjecture,(
% 3.24/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f8,negated_conjecture,(
% 3.24/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 3.24/0.99    inference(negated_conjecture,[],[f7])).
% 3.24/0.99  
% 3.24/0.99  fof(f20,plain,(
% 3.24/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.24/0.99    inference(ennf_transformation,[],[f8])).
% 3.24/0.99  
% 3.24/0.99  fof(f21,plain,(
% 3.24/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.24/0.99    inference(flattening,[],[f20])).
% 3.24/0.99  
% 3.24/0.99  fof(f27,plain,(
% 3.24/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,sK4,X3)),k2_tmap_1(X0,X1,sK4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.24/0.99    introduced(choice_axiom,[])).
% 3.24/0.99  
% 3.24/0.99  fof(f26,plain,(
% 3.24/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,k2_tmap_1(X0,X1,X4,sK3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.24/0.99    introduced(choice_axiom,[])).
% 3.24/0.99  
% 3.24/0.99  fof(f25,plain,(
% 3.24/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,sK2)) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.24/0.99    introduced(choice_axiom,[])).
% 3.24/0.99  
% 3.24/0.99  fof(f24,plain,(
% 3.24/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,k2_tmap_1(X0,sK1,X4,X3)),k2_tmap_1(X0,sK1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.24/0.99    introduced(choice_axiom,[])).
% 3.24/0.99  
% 3.24/0.99  fof(f23,plain,(
% 3.24/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,k2_tmap_1(sK0,X1,X4,X3)),k2_tmap_1(sK0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.24/0.99    introduced(choice_axiom,[])).
% 3.24/0.99  
% 3.24/0.99  fof(f28,plain,(
% 3.24/0.99    ((((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.24/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f27,f26,f25,f24,f23])).
% 3.24/0.99  
% 3.24/0.99  fof(f47,plain,(
% 3.24/0.99    m1_pre_topc(sK3,sK0)),
% 3.24/0.99    inference(cnf_transformation,[],[f28])).
% 3.24/0.99  
% 3.24/0.99  fof(f50,plain,(
% 3.24/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.24/0.99    inference(cnf_transformation,[],[f28])).
% 3.24/0.99  
% 3.24/0.99  fof(f3,axiom,(
% 3.24/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f13,plain,(
% 3.24/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.24/0.99    inference(ennf_transformation,[],[f3])).
% 3.24/0.99  
% 3.24/0.99  fof(f14,plain,(
% 3.24/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.24/0.99    inference(flattening,[],[f13])).
% 3.24/0.99  
% 3.24/0.99  fof(f32,plain,(
% 3.24/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.24/0.99    inference(cnf_transformation,[],[f14])).
% 3.24/0.99  
% 3.24/0.99  fof(f41,plain,(
% 3.24/0.99    ~v2_struct_0(sK1)),
% 3.24/0.99    inference(cnf_transformation,[],[f28])).
% 3.24/0.99  
% 3.24/0.99  fof(f42,plain,(
% 3.24/0.99    v2_pre_topc(sK1)),
% 3.24/0.99    inference(cnf_transformation,[],[f28])).
% 3.24/0.99  
% 3.24/0.99  fof(f43,plain,(
% 3.24/0.99    l1_pre_topc(sK1)),
% 3.24/0.99    inference(cnf_transformation,[],[f28])).
% 3.24/0.99  
% 3.24/0.99  fof(f48,plain,(
% 3.24/0.99    v1_funct_1(sK4)),
% 3.24/0.99    inference(cnf_transformation,[],[f28])).
% 3.24/0.99  
% 3.24/0.99  fof(f49,plain,(
% 3.24/0.99    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.24/0.99    inference(cnf_transformation,[],[f28])).
% 3.24/0.99  
% 3.24/0.99  fof(f2,axiom,(
% 3.24/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f11,plain,(
% 3.24/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.24/0.99    inference(ennf_transformation,[],[f2])).
% 3.24/0.99  
% 3.24/0.99  fof(f12,plain,(
% 3.24/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.24/0.99    inference(flattening,[],[f11])).
% 3.24/0.99  
% 3.24/0.99  fof(f31,plain,(
% 3.24/0.99    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.24/0.99    inference(cnf_transformation,[],[f12])).
% 3.24/0.99  
% 3.24/0.99  fof(f38,plain,(
% 3.24/0.99    ~v2_struct_0(sK0)),
% 3.24/0.99    inference(cnf_transformation,[],[f28])).
% 3.24/0.99  
% 3.24/0.99  fof(f39,plain,(
% 3.24/0.99    v2_pre_topc(sK0)),
% 3.24/0.99    inference(cnf_transformation,[],[f28])).
% 3.24/0.99  
% 3.24/0.99  fof(f40,plain,(
% 3.24/0.99    l1_pre_topc(sK0)),
% 3.24/0.99    inference(cnf_transformation,[],[f28])).
% 3.24/0.99  
% 3.24/0.99  fof(f5,axiom,(
% 3.24/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f17,plain,(
% 3.24/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.24/0.99    inference(ennf_transformation,[],[f5])).
% 3.24/0.99  
% 3.24/0.99  fof(f36,plain,(
% 3.24/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.24/0.99    inference(cnf_transformation,[],[f17])).
% 3.24/0.99  
% 3.24/0.99  fof(f4,axiom,(
% 3.24/0.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f15,plain,(
% 3.24/0.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.24/0.99    inference(ennf_transformation,[],[f4])).
% 3.24/0.99  
% 3.24/0.99  fof(f16,plain,(
% 3.24/0.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.24/0.99    inference(flattening,[],[f15])).
% 3.24/0.99  
% 3.24/0.99  fof(f35,plain,(
% 3.24/0.99    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.24/0.99    inference(cnf_transformation,[],[f16])).
% 3.24/0.99  
% 3.24/0.99  fof(f1,axiom,(
% 3.24/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f9,plain,(
% 3.24/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.24/0.99    inference(ennf_transformation,[],[f1])).
% 3.24/0.99  
% 3.24/0.99  fof(f10,plain,(
% 3.24/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.24/0.99    inference(flattening,[],[f9])).
% 3.24/0.99  
% 3.24/0.99  fof(f22,plain,(
% 3.24/0.99    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.24/0.99    inference(nnf_transformation,[],[f10])).
% 3.24/0.99  
% 3.24/0.99  fof(f30,plain,(
% 3.24/0.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.24/0.99    inference(cnf_transformation,[],[f22])).
% 3.24/0.99  
% 3.24/0.99  fof(f53,plain,(
% 3.24/0.99    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.24/0.99    inference(equality_resolution,[],[f30])).
% 3.24/0.99  
% 3.24/0.99  fof(f33,plain,(
% 3.24/0.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.24/0.99    inference(cnf_transformation,[],[f16])).
% 3.24/0.99  
% 3.24/0.99  fof(f34,plain,(
% 3.24/0.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.24/0.99    inference(cnf_transformation,[],[f16])).
% 3.24/0.99  
% 3.24/0.99  fof(f52,plain,(
% 3.24/0.99    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))),
% 3.24/0.99    inference(cnf_transformation,[],[f28])).
% 3.24/0.99  
% 3.24/0.99  fof(f51,plain,(
% 3.24/0.99    m1_pre_topc(sK2,sK3)),
% 3.24/0.99    inference(cnf_transformation,[],[f28])).
% 3.24/0.99  
% 3.24/0.99  fof(f46,plain,(
% 3.24/0.99    ~v2_struct_0(sK3)),
% 3.24/0.99    inference(cnf_transformation,[],[f28])).
% 3.24/0.99  
% 3.24/0.99  fof(f45,plain,(
% 3.24/0.99    m1_pre_topc(sK2,sK0)),
% 3.24/0.99    inference(cnf_transformation,[],[f28])).
% 3.24/0.99  
% 3.24/0.99  fof(f44,plain,(
% 3.24/0.99    ~v2_struct_0(sK2)),
% 3.24/0.99    inference(cnf_transformation,[],[f28])).
% 3.24/0.99  
% 3.24/0.99  cnf(c_8,plain,
% 3.24/0.99      ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_tmap_1(X3,X1,X4,X0))
% 3.24/0.99      | r2_funct_2(u1_struct_0(X5),u1_struct_0(X1),k3_tmap_1(X3,X1,X0,X5,X2),k2_tmap_1(X3,X1,X4,X5))
% 3.24/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.24/0.99      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
% 3.24/0.99      | ~ m1_pre_topc(X5,X3)
% 3.24/0.99      | ~ m1_pre_topc(X5,X0)
% 3.24/0.99      | ~ m1_pre_topc(X0,X3)
% 3.24/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.24/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.24/0.99      | v2_struct_0(X3)
% 3.24/0.99      | v2_struct_0(X1)
% 3.24/0.99      | v2_struct_0(X5)
% 3.24/0.99      | v2_struct_0(X0)
% 3.24/0.99      | ~ v2_pre_topc(X1)
% 3.24/0.99      | ~ v2_pre_topc(X3)
% 3.24/0.99      | ~ l1_pre_topc(X1)
% 3.24/0.99      | ~ l1_pre_topc(X3)
% 3.24/0.99      | ~ v1_funct_1(X4)
% 3.24/0.99      | ~ v1_funct_1(X2) ),
% 3.24/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_267,plain,
% 3.24/0.99      ( ~ r2_funct_2(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,k2_tmap_1(X2_47,X1_47,X1_48,X0_47))
% 3.24/0.99      | r2_funct_2(u1_struct_0(X3_47),u1_struct_0(X1_47),k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),k2_tmap_1(X2_47,X1_47,X1_48,X3_47))
% 3.24/0.99      | ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
% 3.24/0.99      | ~ v1_funct_2(X1_48,u1_struct_0(X2_47),u1_struct_0(X1_47))
% 3.24/0.99      | ~ m1_pre_topc(X3_47,X2_47)
% 3.24/0.99      | ~ m1_pre_topc(X3_47,X0_47)
% 3.24/0.99      | ~ m1_pre_topc(X0_47,X2_47)
% 3.24/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
% 3.24/0.99      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_47),u1_struct_0(X1_47))))
% 3.24/0.99      | v2_struct_0(X3_47)
% 3.24/0.99      | v2_struct_0(X1_47)
% 3.24/0.99      | v2_struct_0(X0_47)
% 3.24/0.99      | v2_struct_0(X2_47)
% 3.24/0.99      | ~ v2_pre_topc(X1_47)
% 3.24/0.99      | ~ v2_pre_topc(X2_47)
% 3.24/0.99      | ~ l1_pre_topc(X1_47)
% 3.24/0.99      | ~ l1_pre_topc(X2_47)
% 3.24/0.99      | ~ v1_funct_1(X1_48)
% 3.24/0.99      | ~ v1_funct_1(X0_48) ),
% 3.24/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_1133,plain,
% 3.24/0.99      ( ~ r2_funct_2(u1_struct_0(X0_47),u1_struct_0(sK1),X0_48,k2_tmap_1(X1_47,sK1,X1_48,X0_47))
% 3.24/0.99      | r2_funct_2(u1_struct_0(X2_47),u1_struct_0(sK1),k3_tmap_1(X1_47,sK1,X0_47,X2_47,X0_48),k2_tmap_1(X1_47,sK1,X1_48,X2_47))
% 3.24/0.99      | ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(sK1))
% 3.24/0.99      | ~ v1_funct_2(X1_48,u1_struct_0(X1_47),u1_struct_0(sK1))
% 3.24/0.99      | ~ m1_pre_topc(X2_47,X0_47)
% 3.24/0.99      | ~ m1_pre_topc(X0_47,X1_47)
% 3.24/0.99      | ~ m1_pre_topc(X2_47,X1_47)
% 3.24/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(sK1))))
% 3.24/0.99      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_47),u1_struct_0(sK1))))
% 3.24/0.99      | v2_struct_0(X1_47)
% 3.24/0.99      | v2_struct_0(X0_47)
% 3.24/0.99      | v2_struct_0(X2_47)
% 3.24/0.99      | v2_struct_0(sK1)
% 3.24/0.99      | ~ v2_pre_topc(X1_47)
% 3.24/0.99      | ~ v2_pre_topc(sK1)
% 3.24/0.99      | ~ l1_pre_topc(X1_47)
% 3.24/0.99      | ~ l1_pre_topc(sK1)
% 3.24/0.99      | ~ v1_funct_1(X1_48)
% 3.24/0.99      | ~ v1_funct_1(X0_48) ),
% 3.24/0.99      inference(instantiation,[status(thm)],[c_267]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_1275,plain,
% 3.24/0.99      ( r2_funct_2(u1_struct_0(X0_47),u1_struct_0(sK1),k3_tmap_1(X1_47,sK1,X2_47,X0_47,k2_tmap_1(X1_47,sK1,X0_48,X2_47)),k2_tmap_1(X1_47,sK1,X0_48,X0_47))
% 3.24/0.99      | ~ r2_funct_2(u1_struct_0(X2_47),u1_struct_0(sK1),k2_tmap_1(X1_47,sK1,X0_48,X2_47),k2_tmap_1(X1_47,sK1,X0_48,X2_47))
% 3.24/0.99      | ~ v1_funct_2(X0_48,u1_struct_0(X1_47),u1_struct_0(sK1))
% 3.24/0.99      | ~ v1_funct_2(k2_tmap_1(X1_47,sK1,X0_48,X2_47),u1_struct_0(X2_47),u1_struct_0(sK1))
% 3.24/0.99      | ~ m1_pre_topc(X0_47,X2_47)
% 3.24/0.99      | ~ m1_pre_topc(X2_47,X1_47)
% 3.24/0.99      | ~ m1_pre_topc(X0_47,X1_47)
% 3.24/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_47),u1_struct_0(sK1))))
% 3.24/0.99      | ~ m1_subset_1(k2_tmap_1(X1_47,sK1,X0_48,X2_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_47),u1_struct_0(sK1))))
% 3.24/0.99      | v2_struct_0(X1_47)
% 3.24/0.99      | v2_struct_0(X2_47)
% 3.24/0.99      | v2_struct_0(X0_47)
% 3.24/0.99      | v2_struct_0(sK1)
% 3.24/0.99      | ~ v2_pre_topc(X1_47)
% 3.24/0.99      | ~ v2_pre_topc(sK1)
% 3.24/0.99      | ~ l1_pre_topc(X1_47)
% 3.24/0.99      | ~ l1_pre_topc(sK1)
% 3.24/0.99      | ~ v1_funct_1(X0_48)
% 3.24/0.99      | ~ v1_funct_1(k2_tmap_1(X1_47,sK1,X0_48,X2_47)) ),
% 3.24/0.99      inference(instantiation,[status(thm)],[c_1133]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_8485,plain,
% 3.24/0.99      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3))
% 3.24/0.99      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
% 3.24/0.99      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.24/0.99      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.24/0.99      | ~ m1_pre_topc(sK3,sK0)
% 3.24/0.99      | ~ m1_pre_topc(sK2,sK3)
% 3.24/0.99      | ~ m1_pre_topc(sK2,sK0)
% 3.24/0.99      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.24/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.24/0.99      | v2_struct_0(sK3)
% 3.24/0.99      | v2_struct_0(sK0)
% 3.24/0.99      | v2_struct_0(sK1)
% 3.24/0.99      | v2_struct_0(sK2)
% 3.24/0.99      | ~ v2_pre_topc(sK0)
% 3.24/0.99      | ~ v2_pre_topc(sK1)
% 3.24/0.99      | ~ l1_pre_topc(sK0)
% 3.24/0.99      | ~ l1_pre_topc(sK1)
% 3.24/0.99      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
% 3.24/0.99      | ~ v1_funct_1(sK4) ),
% 3.24/0.99      inference(instantiation,[status(thm)],[c_1275]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_14,negated_conjecture,
% 3.24/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.24/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_261,negated_conjecture,
% 3.24/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.24/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_711,plain,
% 3.24/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_261]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_11,negated_conjecture,
% 3.24/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.24/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_264,negated_conjecture,
% 3.24/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.24/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_708,plain,
% 3.24/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_264]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_3,plain,
% 3.24/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.24/0.99      | ~ m1_pre_topc(X3,X4)
% 3.24/0.99      | ~ m1_pre_topc(X3,X1)
% 3.24/0.99      | ~ m1_pre_topc(X1,X4)
% 3.24/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.24/0.99      | v2_struct_0(X4)
% 3.24/0.99      | v2_struct_0(X2)
% 3.24/0.99      | ~ v2_pre_topc(X2)
% 3.24/0.99      | ~ v2_pre_topc(X4)
% 3.24/0.99      | ~ l1_pre_topc(X2)
% 3.24/0.99      | ~ l1_pre_topc(X4)
% 3.24/0.99      | ~ v1_funct_1(X0)
% 3.24/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.24/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_272,plain,
% 3.24/0.99      ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
% 3.24/0.99      | ~ m1_pre_topc(X0_47,X2_47)
% 3.24/0.99      | ~ m1_pre_topc(X3_47,X2_47)
% 3.24/0.99      | ~ m1_pre_topc(X3_47,X0_47)
% 3.24/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
% 3.24/0.99      | v2_struct_0(X2_47)
% 3.24/0.99      | v2_struct_0(X1_47)
% 3.24/0.99      | ~ v2_pre_topc(X1_47)
% 3.24/0.99      | ~ v2_pre_topc(X2_47)
% 3.24/0.99      | ~ l1_pre_topc(X1_47)
% 3.24/0.99      | ~ l1_pre_topc(X2_47)
% 3.24/0.99      | ~ v1_funct_1(X0_48)
% 3.24/0.99      | k2_partfun1(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,u1_struct_0(X3_47)) = k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48) ),
% 3.24/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_700,plain,
% 3.24/0.99      ( k2_partfun1(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,u1_struct_0(X2_47)) = k3_tmap_1(X3_47,X1_47,X0_47,X2_47,X0_48)
% 3.24/0.99      | v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
% 3.24/0.99      | m1_pre_topc(X2_47,X0_47) != iProver_top
% 3.24/0.99      | m1_pre_topc(X0_47,X3_47) != iProver_top
% 3.24/0.99      | m1_pre_topc(X2_47,X3_47) != iProver_top
% 3.24/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
% 3.24/0.99      | v2_struct_0(X1_47) = iProver_top
% 3.24/0.99      | v2_struct_0(X3_47) = iProver_top
% 3.24/0.99      | v2_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | v2_pre_topc(X3_47) != iProver_top
% 3.24/0.99      | l1_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | l1_pre_topc(X3_47) != iProver_top
% 3.24/0.99      | v1_funct_1(X0_48) != iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_1961,plain,
% 3.24/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)
% 3.24/0.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.24/0.99      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 3.24/0.99      | m1_pre_topc(X0_47,sK0) != iProver_top
% 3.24/0.99      | m1_pre_topc(sK0,X1_47) != iProver_top
% 3.24/0.99      | v2_struct_0(X1_47) = iProver_top
% 3.24/0.99      | v2_struct_0(sK1) = iProver_top
% 3.24/0.99      | v2_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.24/0.99      | l1_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.24/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.24/0.99      inference(superposition,[status(thm)],[c_708,c_700]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_20,negated_conjecture,
% 3.24/0.99      ( ~ v2_struct_0(sK1) ),
% 3.24/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_27,plain,
% 3.24/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_19,negated_conjecture,
% 3.24/0.99      ( v2_pre_topc(sK1) ),
% 3.24/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_28,plain,
% 3.24/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_18,negated_conjecture,
% 3.24/0.99      ( l1_pre_topc(sK1) ),
% 3.24/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_29,plain,
% 3.24/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_13,negated_conjecture,
% 3.24/0.99      ( v1_funct_1(sK4) ),
% 3.24/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_34,plain,
% 3.24/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_12,negated_conjecture,
% 3.24/0.99      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.24/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_35,plain,
% 3.24/0.99      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_2328,plain,
% 3.24/0.99      ( v2_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)
% 3.24/0.99      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 3.24/0.99      | m1_pre_topc(X0_47,sK0) != iProver_top
% 3.24/0.99      | m1_pre_topc(sK0,X1_47) != iProver_top
% 3.24/0.99      | v2_struct_0(X1_47) = iProver_top
% 3.24/0.99      | l1_pre_topc(X1_47) != iProver_top ),
% 3.24/0.99      inference(global_propositional_subsumption,
% 3.24/0.99                [status(thm)],
% 3.24/0.99                [c_1961,c_27,c_28,c_29,c_34,c_35,c_36,c_1031]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_2329,plain,
% 3.24/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)
% 3.24/0.99      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 3.24/0.99      | m1_pre_topc(X0_47,sK0) != iProver_top
% 3.24/0.99      | m1_pre_topc(sK0,X1_47) != iProver_top
% 3.24/0.99      | v2_struct_0(X1_47) = iProver_top
% 3.24/0.99      | v2_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | l1_pre_topc(X1_47) != iProver_top ),
% 3.24/0.99      inference(renaming,[status(thm)],[c_2328]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_2342,plain,
% 3.24/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
% 3.24/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.24/0.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.24/0.99      | v2_struct_0(sK0) = iProver_top
% 3.24/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.24/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.24/0.99      inference(superposition,[status(thm)],[c_711,c_2329]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_2,plain,
% 3.24/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.24/0.99      | ~ m1_pre_topc(X3,X1)
% 3.24/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.24/0.99      | v2_struct_0(X1)
% 3.24/0.99      | v2_struct_0(X2)
% 3.24/0.99      | ~ v2_pre_topc(X2)
% 3.24/0.99      | ~ v2_pre_topc(X1)
% 3.24/0.99      | ~ l1_pre_topc(X2)
% 3.24/0.99      | ~ l1_pre_topc(X1)
% 3.24/0.99      | ~ v1_funct_1(X0)
% 3.24/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.24/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_273,plain,
% 3.24/0.99      ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
% 3.24/0.99      | ~ m1_pre_topc(X2_47,X0_47)
% 3.24/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
% 3.24/0.99      | v2_struct_0(X1_47)
% 3.24/0.99      | v2_struct_0(X0_47)
% 3.24/0.99      | ~ v2_pre_topc(X1_47)
% 3.24/0.99      | ~ v2_pre_topc(X0_47)
% 3.24/0.99      | ~ l1_pre_topc(X1_47)
% 3.24/0.99      | ~ l1_pre_topc(X0_47)
% 3.24/0.99      | ~ v1_funct_1(X0_48)
% 3.24/0.99      | k2_partfun1(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,u1_struct_0(X2_47)) = k2_tmap_1(X0_47,X1_47,X0_48,X2_47) ),
% 3.24/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_699,plain,
% 3.24/0.99      ( k2_partfun1(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,u1_struct_0(X2_47)) = k2_tmap_1(X0_47,X1_47,X0_48,X2_47)
% 3.24/0.99      | v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
% 3.24/0.99      | m1_pre_topc(X2_47,X0_47) != iProver_top
% 3.24/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
% 3.24/0.99      | v2_struct_0(X1_47) = iProver_top
% 3.24/0.99      | v2_struct_0(X0_47) = iProver_top
% 3.24/0.99      | v2_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | v2_pre_topc(X0_47) != iProver_top
% 3.24/0.99      | l1_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | l1_pre_topc(X0_47) != iProver_top
% 3.24/0.99      | v1_funct_1(X0_48) != iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_273]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_1604,plain,
% 3.24/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k2_tmap_1(sK0,sK1,sK4,X0_47)
% 3.24/0.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.24/0.99      | m1_pre_topc(X0_47,sK0) != iProver_top
% 3.24/0.99      | v2_struct_0(sK0) = iProver_top
% 3.24/0.99      | v2_struct_0(sK1) = iProver_top
% 3.24/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.24/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.24/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.24/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.24/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.24/0.99      inference(superposition,[status(thm)],[c_708,c_699]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_23,negated_conjecture,
% 3.24/0.99      ( ~ v2_struct_0(sK0) ),
% 3.24/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_24,plain,
% 3.24/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_22,negated_conjecture,
% 3.24/0.99      ( v2_pre_topc(sK0) ),
% 3.24/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_25,plain,
% 3.24/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_21,negated_conjecture,
% 3.24/0.99      ( l1_pre_topc(sK0) ),
% 3.24/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_26,plain,
% 3.24/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_2034,plain,
% 3.24/0.99      ( m1_pre_topc(X0_47,sK0) != iProver_top
% 3.24/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k2_tmap_1(sK0,sK1,sK4,X0_47) ),
% 3.24/0.99      inference(global_propositional_subsumption,
% 3.24/0.99                [status(thm)],
% 3.24/0.99                [c_1604,c_24,c_25,c_26,c_27,c_28,c_29,c_34,c_35]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_2035,plain,
% 3.24/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k2_tmap_1(sK0,sK1,sK4,X0_47)
% 3.24/0.99      | m1_pre_topc(X0_47,sK0) != iProver_top ),
% 3.24/0.99      inference(renaming,[status(thm)],[c_2034]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_2042,plain,
% 3.24/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 3.24/0.99      inference(superposition,[status(thm)],[c_711,c_2035]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_2376,plain,
% 3.24/0.99      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
% 3.24/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.24/0.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.24/0.99      | v2_struct_0(sK0) = iProver_top
% 3.24/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.24/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.24/0.99      inference(light_normalisation,[status(thm)],[c_2342,c_2042]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_33,plain,
% 3.24/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_7,plain,
% 3.24/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.24/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_42,plain,
% 3.24/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.24/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_44,plain,
% 3.24/0.99      ( m1_pre_topc(sK0,sK0) = iProver_top
% 3.24/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.24/0.99      inference(instantiation,[status(thm)],[c_42]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_3511,plain,
% 3.24/0.99      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 3.24/0.99      inference(global_propositional_subsumption,
% 3.24/0.99                [status(thm)],
% 3.24/0.99                [c_2376,c_24,c_25,c_26,c_33,c_44]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_4,plain,
% 3.24/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.24/0.99      | ~ m1_pre_topc(X3,X4)
% 3.24/0.99      | ~ m1_pre_topc(X1,X4)
% 3.24/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.24/0.99      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 3.24/0.99      | v2_struct_0(X4)
% 3.24/0.99      | v2_struct_0(X2)
% 3.24/0.99      | ~ v2_pre_topc(X2)
% 3.24/0.99      | ~ v2_pre_topc(X4)
% 3.24/0.99      | ~ l1_pre_topc(X2)
% 3.24/0.99      | ~ l1_pre_topc(X4)
% 3.24/0.99      | ~ v1_funct_1(X0) ),
% 3.24/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_271,plain,
% 3.24/0.99      ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
% 3.24/0.99      | ~ m1_pre_topc(X0_47,X2_47)
% 3.24/0.99      | ~ m1_pre_topc(X3_47,X2_47)
% 3.24/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
% 3.24/0.99      | m1_subset_1(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_47),u1_struct_0(X1_47))))
% 3.24/0.99      | v2_struct_0(X2_47)
% 3.24/0.99      | v2_struct_0(X1_47)
% 3.24/0.99      | ~ v2_pre_topc(X1_47)
% 3.24/0.99      | ~ v2_pre_topc(X2_47)
% 3.24/0.99      | ~ l1_pre_topc(X1_47)
% 3.24/0.99      | ~ l1_pre_topc(X2_47)
% 3.24/0.99      | ~ v1_funct_1(X0_48) ),
% 3.24/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_701,plain,
% 3.24/0.99      ( v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
% 3.24/0.99      | m1_pre_topc(X0_47,X2_47) != iProver_top
% 3.24/0.99      | m1_pre_topc(X3_47,X2_47) != iProver_top
% 3.24/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
% 3.24/0.99      | m1_subset_1(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_47),u1_struct_0(X1_47)))) = iProver_top
% 3.24/0.99      | v2_struct_0(X1_47) = iProver_top
% 3.24/0.99      | v2_struct_0(X2_47) = iProver_top
% 3.24/0.99      | v2_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | v2_pre_topc(X2_47) != iProver_top
% 3.24/0.99      | l1_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | l1_pre_topc(X2_47) != iProver_top
% 3.24/0.99      | v1_funct_1(X0_48) != iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_271]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_3514,plain,
% 3.24/0.99      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.24/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.24/0.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.24/0.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 3.24/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.24/0.99      | v2_struct_0(sK0) = iProver_top
% 3.24/0.99      | v2_struct_0(sK1) = iProver_top
% 3.24/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.24/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.24/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.24/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.24/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.24/0.99      inference(superposition,[status(thm)],[c_3511,c_701]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_36,plain,
% 3.24/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_5021,plain,
% 3.24/0.99      ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.24/0.99      inference(global_propositional_subsumption,
% 3.24/0.99                [status(thm)],
% 3.24/0.99                [c_3514,c_24,c_25,c_26,c_27,c_28,c_29,c_33,c_34,c_35,
% 3.24/0.99                 c_36,c_44]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_0,plain,
% 3.24/0.99      ( r2_funct_2(X0,X1,X2,X2)
% 3.24/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.24/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.24/0.99      | ~ v1_funct_1(X2) ),
% 3.24/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_275,plain,
% 3.24/0.99      ( r2_funct_2(X0_49,X1_49,X0_48,X0_48)
% 3.24/0.99      | ~ v1_funct_2(X0_48,X0_49,X1_49)
% 3.24/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.24/0.99      | ~ v1_funct_1(X0_48) ),
% 3.24/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_697,plain,
% 3.24/0.99      ( r2_funct_2(X0_49,X1_49,X0_48,X0_48) = iProver_top
% 3.24/0.99      | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 3.24/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.24/0.99      | v1_funct_1(X0_48) != iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_275]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_5030,plain,
% 3.24/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top
% 3.24/0.99      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.24/0.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 3.24/0.99      inference(superposition,[status(thm)],[c_5021,c_697]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_5129,plain,
% 3.24/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3))
% 3.24/0.99      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.24/0.99      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 3.24/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5030]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_6,plain,
% 3.24/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.24/0.99      | ~ m1_pre_topc(X3,X4)
% 3.24/0.99      | ~ m1_pre_topc(X1,X4)
% 3.24/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.24/0.99      | v2_struct_0(X4)
% 3.24/0.99      | v2_struct_0(X2)
% 3.24/0.99      | ~ v2_pre_topc(X2)
% 3.24/0.99      | ~ v2_pre_topc(X4)
% 3.24/0.99      | ~ l1_pre_topc(X2)
% 3.24/0.99      | ~ l1_pre_topc(X4)
% 3.24/0.99      | ~ v1_funct_1(X0)
% 3.24/0.99      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 3.24/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_269,plain,
% 3.24/0.99      ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
% 3.24/0.99      | ~ m1_pre_topc(X0_47,X2_47)
% 3.24/0.99      | ~ m1_pre_topc(X3_47,X2_47)
% 3.24/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
% 3.24/0.99      | v2_struct_0(X2_47)
% 3.24/0.99      | v2_struct_0(X1_47)
% 3.24/0.99      | ~ v2_pre_topc(X1_47)
% 3.24/0.99      | ~ v2_pre_topc(X2_47)
% 3.24/0.99      | ~ l1_pre_topc(X1_47)
% 3.24/0.99      | ~ l1_pre_topc(X2_47)
% 3.24/0.99      | ~ v1_funct_1(X0_48)
% 3.24/0.99      | v1_funct_1(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48)) ),
% 3.24/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_703,plain,
% 3.24/0.99      ( v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
% 3.24/0.99      | m1_pre_topc(X0_47,X2_47) != iProver_top
% 3.24/0.99      | m1_pre_topc(X3_47,X2_47) != iProver_top
% 3.24/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
% 3.24/0.99      | v2_struct_0(X1_47) = iProver_top
% 3.24/0.99      | v2_struct_0(X2_47) = iProver_top
% 3.24/0.99      | v2_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | v2_pre_topc(X2_47) != iProver_top
% 3.24/0.99      | l1_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | l1_pre_topc(X2_47) != iProver_top
% 3.24/0.99      | v1_funct_1(X0_48) != iProver_top
% 3.24/0.99      | v1_funct_1(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48)) = iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_269]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_1621,plain,
% 3.24/0.99      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.24/0.99      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 3.24/0.99      | m1_pre_topc(sK0,X1_47) != iProver_top
% 3.24/0.99      | v2_struct_0(X1_47) = iProver_top
% 3.24/0.99      | v2_struct_0(sK1) = iProver_top
% 3.24/0.99      | v2_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.24/0.99      | l1_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.24/0.99      | v1_funct_1(k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)) = iProver_top
% 3.24/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.24/0.99      inference(superposition,[status(thm)],[c_708,c_703]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_1006,plain,
% 3.24/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.24/0.99      | ~ m1_pre_topc(X0_47,X1_47)
% 3.24/0.99      | ~ m1_pre_topc(sK0,X1_47)
% 3.24/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.24/0.99      | v2_struct_0(X1_47)
% 3.24/0.99      | v2_struct_0(sK1)
% 3.24/0.99      | ~ v2_pre_topc(X1_47)
% 3.24/0.99      | ~ v2_pre_topc(sK1)
% 3.24/0.99      | ~ l1_pre_topc(X1_47)
% 3.24/0.99      | ~ l1_pre_topc(sK1)
% 3.24/0.99      | v1_funct_1(k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4))
% 3.24/0.99      | ~ v1_funct_1(sK4) ),
% 3.24/0.99      inference(instantiation,[status(thm)],[c_269]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_1007,plain,
% 3.24/0.99      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.24/0.99      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 3.24/0.99      | m1_pre_topc(sK0,X1_47) != iProver_top
% 3.24/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.24/0.99      | v2_struct_0(X1_47) = iProver_top
% 3.24/0.99      | v2_struct_0(sK1) = iProver_top
% 3.24/0.99      | v2_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.24/0.99      | l1_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.24/0.99      | v1_funct_1(k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)) = iProver_top
% 3.24/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_1006]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_2315,plain,
% 3.24/0.99      ( v1_funct_1(k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)) = iProver_top
% 3.24/0.99      | v2_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 3.24/0.99      | m1_pre_topc(sK0,X1_47) != iProver_top
% 3.24/0.99      | v2_struct_0(X1_47) = iProver_top
% 3.24/0.99      | l1_pre_topc(X1_47) != iProver_top ),
% 3.24/0.99      inference(global_propositional_subsumption,
% 3.24/0.99                [status(thm)],
% 3.24/0.99                [c_1621,c_27,c_28,c_29,c_34,c_35]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_2316,plain,
% 3.24/0.99      ( m1_pre_topc(X0_47,X1_47) != iProver_top
% 3.24/0.99      | m1_pre_topc(sK0,X1_47) != iProver_top
% 3.24/0.99      | v2_struct_0(X1_47) = iProver_top
% 3.24/0.99      | v2_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | l1_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | v1_funct_1(k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)) = iProver_top ),
% 3.24/0.99      inference(renaming,[status(thm)],[c_2315]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_3516,plain,
% 3.24/0.99      ( m1_pre_topc(sK3,sK0) != iProver_top
% 3.24/0.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.24/0.99      | v2_struct_0(sK0) = iProver_top
% 3.24/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.24/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.24/0.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
% 3.24/0.99      inference(superposition,[status(thm)],[c_3511,c_2316]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_3579,plain,
% 3.24/0.99      ( ~ m1_pre_topc(sK3,sK0)
% 3.24/0.99      | ~ m1_pre_topc(sK0,sK0)
% 3.24/0.99      | v2_struct_0(sK0)
% 3.24/0.99      | ~ v2_pre_topc(sK0)
% 3.24/0.99      | ~ l1_pre_topc(sK0)
% 3.24/0.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 3.24/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3516]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_5,plain,
% 3.24/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.24/0.99      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 3.24/0.99      | ~ m1_pre_topc(X4,X3)
% 3.24/0.99      | ~ m1_pre_topc(X1,X3)
% 3.24/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.24/0.99      | v2_struct_0(X3)
% 3.24/0.99      | v2_struct_0(X2)
% 3.24/0.99      | ~ v2_pre_topc(X2)
% 3.24/0.99      | ~ v2_pre_topc(X3)
% 3.24/0.99      | ~ l1_pre_topc(X2)
% 3.24/0.99      | ~ l1_pre_topc(X3)
% 3.24/0.99      | ~ v1_funct_1(X0) ),
% 3.24/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_270,plain,
% 3.24/0.99      ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
% 3.24/0.99      | v1_funct_2(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),u1_struct_0(X3_47),u1_struct_0(X1_47))
% 3.24/0.99      | ~ m1_pre_topc(X3_47,X2_47)
% 3.24/0.99      | ~ m1_pre_topc(X0_47,X2_47)
% 3.24/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
% 3.24/0.99      | v2_struct_0(X1_47)
% 3.24/0.99      | v2_struct_0(X2_47)
% 3.24/0.99      | ~ v2_pre_topc(X1_47)
% 3.24/0.99      | ~ v2_pre_topc(X2_47)
% 3.24/0.99      | ~ l1_pre_topc(X1_47)
% 3.24/0.99      | ~ l1_pre_topc(X2_47)
% 3.24/0.99      | ~ v1_funct_1(X0_48) ),
% 3.24/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_702,plain,
% 3.24/0.99      ( v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
% 3.24/0.99      | v1_funct_2(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),u1_struct_0(X3_47),u1_struct_0(X1_47)) = iProver_top
% 3.24/0.99      | m1_pre_topc(X0_47,X2_47) != iProver_top
% 3.24/0.99      | m1_pre_topc(X3_47,X2_47) != iProver_top
% 3.24/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
% 3.24/0.99      | v2_struct_0(X1_47) = iProver_top
% 3.24/0.99      | v2_struct_0(X2_47) = iProver_top
% 3.24/0.99      | v2_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | v2_pre_topc(X2_47) != iProver_top
% 3.24/0.99      | l1_pre_topc(X1_47) != iProver_top
% 3.24/0.99      | l1_pre_topc(X2_47) != iProver_top
% 3.24/0.99      | v1_funct_1(X0_48) != iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_3515,plain,
% 3.24/0.99      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 3.24/0.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.24/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.24/0.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.24/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.24/0.99      | v2_struct_0(sK0) = iProver_top
% 3.24/0.99      | v2_struct_0(sK1) = iProver_top
% 3.24/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.24/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.24/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.24/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.24/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.24/0.99      inference(superposition,[status(thm)],[c_3511,c_702]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_3578,plain,
% 3.24/0.99      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.24/0.99      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.24/0.99      | ~ m1_pre_topc(sK3,sK0)
% 3.24/0.99      | ~ m1_pre_topc(sK0,sK0)
% 3.24/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.24/0.99      | v2_struct_0(sK0)
% 3.24/0.99      | v2_struct_0(sK1)
% 3.24/0.99      | ~ v2_pre_topc(sK0)
% 3.24/0.99      | ~ v2_pre_topc(sK1)
% 3.24/0.99      | ~ l1_pre_topc(sK0)
% 3.24/0.99      | ~ l1_pre_topc(sK1)
% 3.24/0.99      | ~ v1_funct_1(sK4) ),
% 3.24/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3515]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_3577,plain,
% 3.24/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.24/0.99      | ~ m1_pre_topc(sK3,sK0)
% 3.24/0.99      | ~ m1_pre_topc(sK0,sK0)
% 3.24/0.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.24/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.24/0.99      | v2_struct_0(sK0)
% 3.24/0.99      | v2_struct_0(sK1)
% 3.24/0.99      | ~ v2_pre_topc(sK0)
% 3.24/0.99      | ~ v2_pre_topc(sK1)
% 3.24/0.99      | ~ l1_pre_topc(sK0)
% 3.24/0.99      | ~ l1_pre_topc(sK1)
% 3.24/0.99      | ~ v1_funct_1(sK4) ),
% 3.24/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3514]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_43,plain,
% 3.24/0.99      ( m1_pre_topc(sK0,sK0) | ~ l1_pre_topc(sK0) ),
% 3.24/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_9,negated_conjecture,
% 3.24/0.99      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) ),
% 3.24/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_10,negated_conjecture,
% 3.24/0.99      ( m1_pre_topc(sK2,sK3) ),
% 3.24/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_15,negated_conjecture,
% 3.24/0.99      ( ~ v2_struct_0(sK3) ),
% 3.24/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_16,negated_conjecture,
% 3.24/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.24/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_17,negated_conjecture,
% 3.24/0.99      ( ~ v2_struct_0(sK2) ),
% 3.24/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(contradiction,plain,
% 3.24/0.99      ( $false ),
% 3.24/0.99      inference(minisat,
% 3.24/0.99                [status(thm)],
% 3.24/0.99                [c_8485,c_5129,c_3579,c_3578,c_3577,c_43,c_9,c_10,c_11,
% 3.24/0.99                 c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,
% 3.24/0.99                 c_23]) ).
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.24/0.99  
% 3.24/0.99  ------                               Statistics
% 3.24/0.99  
% 3.24/0.99  ------ General
% 3.24/0.99  
% 3.24/0.99  abstr_ref_over_cycles:                  0
% 3.24/0.99  abstr_ref_under_cycles:                 0
% 3.24/0.99  gc_basic_clause_elim:                   0
% 3.24/0.99  forced_gc_time:                         0
% 3.24/0.99  parsing_time:                           0.012
% 3.24/0.99  unif_index_cands_time:                  0.
% 3.24/0.99  unif_index_add_time:                    0.
% 3.24/0.99  orderings_time:                         0.
% 3.24/0.99  out_proof_time:                         0.011
% 3.24/0.99  total_time:                             0.335
% 3.24/0.99  num_of_symbols:                         52
% 3.24/0.99  num_of_terms:                           7861
% 3.24/0.99  
% 3.24/0.99  ------ Preprocessing
% 3.24/0.99  
% 3.24/0.99  num_of_splits:                          0
% 3.24/0.99  num_of_split_atoms:                     0
% 3.24/0.99  num_of_reused_defs:                     0
% 3.24/0.99  num_eq_ax_congr_red:                    26
% 3.24/0.99  num_of_sem_filtered_clauses:            1
% 3.24/0.99  num_of_subtypes:                        5
% 3.24/0.99  monotx_restored_types:                  0
% 3.24/0.99  sat_num_of_epr_types:                   0
% 3.24/0.99  sat_num_of_non_cyclic_types:            0
% 3.24/0.99  sat_guarded_non_collapsed_types:        1
% 3.24/0.99  num_pure_diseq_elim:                    0
% 3.24/0.99  simp_replaced_by:                       0
% 3.24/0.99  res_preprocessed:                       89
% 3.24/0.99  prep_upred:                             0
% 3.24/0.99  prep_unflattend:                        0
% 3.24/0.99  smt_new_axioms:                         0
% 3.24/0.99  pred_elim_cands:                        8
% 3.24/0.99  pred_elim:                              0
% 3.24/0.99  pred_elim_cl:                           0
% 3.24/0.99  pred_elim_cycles:                       1
% 3.24/0.99  merged_defs:                            0
% 3.24/0.99  merged_defs_ncl:                        0
% 3.24/0.99  bin_hyper_res:                          0
% 3.24/0.99  prep_cycles:                            3
% 3.24/0.99  pred_elim_time:                         0.
% 3.24/0.99  splitting_time:                         0.
% 3.24/0.99  sem_filter_time:                        0.
% 3.24/0.99  monotx_time:                            0.
% 3.24/0.99  subtype_inf_time:                       0.
% 3.24/0.99  
% 3.24/0.99  ------ Problem properties
% 3.24/0.99  
% 3.24/0.99  clauses:                                24
% 3.24/0.99  conjectures:                            15
% 3.24/0.99  epr:                                    13
% 3.24/0.99  horn:                                   18
% 3.24/0.99  ground:                                 15
% 3.24/0.99  unary:                                  15
% 3.24/0.99  binary:                                 1
% 3.24/0.99  lits:                                   108
% 3.24/0.99  lits_eq:                                3
% 3.24/0.99  fd_pure:                                0
% 3.24/0.99  fd_pseudo:                              0
% 3.24/0.99  fd_cond:                                0
% 3.24/0.99  fd_pseudo_cond:                         1
% 3.24/0.99  ac_symbols:                             0
% 3.24/0.99  
% 3.24/0.99  ------ Propositional Solver
% 3.24/0.99  
% 3.24/0.99  prop_solver_calls:                      26
% 3.24/0.99  prop_fast_solver_calls:                 1585
% 3.24/0.99  smt_solver_calls:                       0
% 3.24/0.99  smt_fast_solver_calls:                  0
% 3.24/0.99  prop_num_of_clauses:                    2175
% 3.24/0.99  prop_preprocess_simplified:             6668
% 3.24/0.99  prop_fo_subsumed:                       234
% 3.24/0.99  prop_solver_time:                       0.
% 3.24/0.99  smt_solver_time:                        0.
% 3.24/0.99  smt_fast_solver_time:                   0.
% 3.24/0.99  prop_fast_solver_time:                  0.
% 3.24/0.99  prop_unsat_core_time:                   0.
% 3.24/0.99  
% 3.24/0.99  ------ QBF
% 3.24/0.99  
% 3.24/0.99  qbf_q_res:                              0
% 3.24/0.99  qbf_num_tautologies:                    0
% 3.24/0.99  qbf_prep_cycles:                        0
% 3.24/0.99  
% 3.24/0.99  ------ BMC1
% 3.24/0.99  
% 3.24/0.99  bmc1_current_bound:                     -1
% 3.24/0.99  bmc1_last_solved_bound:                 -1
% 3.24/0.99  bmc1_unsat_core_size:                   -1
% 3.24/0.99  bmc1_unsat_core_parents_size:           -1
% 3.24/0.99  bmc1_merge_next_fun:                    0
% 3.24/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.24/0.99  
% 3.24/0.99  ------ Instantiation
% 3.24/0.99  
% 3.24/0.99  inst_num_of_clauses:                    860
% 3.24/0.99  inst_num_in_passive:                    197
% 3.24/0.99  inst_num_in_active:                     379
% 3.24/0.99  inst_num_in_unprocessed:                283
% 3.24/0.99  inst_num_of_loops:                      411
% 3.24/0.99  inst_num_of_learning_restarts:          0
% 3.24/0.99  inst_num_moves_active_passive:          25
% 3.24/0.99  inst_lit_activity:                      0
% 3.24/0.99  inst_lit_activity_moves:                0
% 3.24/0.99  inst_num_tautologies:                   0
% 3.24/0.99  inst_num_prop_implied:                  0
% 3.24/0.99  inst_num_existing_simplified:           0
% 3.24/0.99  inst_num_eq_res_simplified:             0
% 3.24/0.99  inst_num_child_elim:                    0
% 3.24/0.99  inst_num_of_dismatching_blockings:      651
% 3.24/0.99  inst_num_of_non_proper_insts:           1435
% 3.24/0.99  inst_num_of_duplicates:                 0
% 3.24/0.99  inst_inst_num_from_inst_to_res:         0
% 3.24/0.99  inst_dismatching_checking_time:         0.
% 3.24/0.99  
% 3.24/0.99  ------ Resolution
% 3.24/0.99  
% 3.24/0.99  res_num_of_clauses:                     0
% 3.24/0.99  res_num_in_passive:                     0
% 3.24/0.99  res_num_in_active:                      0
% 3.24/0.99  res_num_of_loops:                       92
% 3.24/0.99  res_forward_subset_subsumed:            111
% 3.24/0.99  res_backward_subset_subsumed:           0
% 3.24/0.99  res_forward_subsumed:                   0
% 3.24/0.99  res_backward_subsumed:                  0
% 3.24/0.99  res_forward_subsumption_resolution:     0
% 3.24/0.99  res_backward_subsumption_resolution:    0
% 3.24/0.99  res_clause_to_clause_subsumption:       502
% 3.24/0.99  res_orphan_elimination:                 0
% 3.24/0.99  res_tautology_del:                      138
% 3.24/0.99  res_num_eq_res_simplified:              0
% 3.24/0.99  res_num_sel_changes:                    0
% 3.24/0.99  res_moves_from_active_to_pass:          0
% 3.24/0.99  
% 3.24/0.99  ------ Superposition
% 3.24/0.99  
% 3.24/0.99  sup_time_total:                         0.
% 3.24/0.99  sup_time_generating:                    0.
% 3.24/0.99  sup_time_sim_full:                      0.
% 3.24/0.99  sup_time_sim_immed:                     0.
% 3.24/0.99  
% 3.24/0.99  sup_num_of_clauses:                     101
% 3.24/0.99  sup_num_in_active:                      82
% 3.24/0.99  sup_num_in_passive:                     19
% 3.24/0.99  sup_num_of_loops:                       82
% 3.24/0.99  sup_fw_superposition:                   60
% 3.24/0.99  sup_bw_superposition:                   36
% 3.24/0.99  sup_immediate_simplified:               20
% 3.24/0.99  sup_given_eliminated:                   0
% 3.24/0.99  comparisons_done:                       0
% 3.24/0.99  comparisons_avoided:                    0
% 3.24/0.99  
% 3.24/0.99  ------ Simplifications
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  sim_fw_subset_subsumed:                 3
% 3.24/0.99  sim_bw_subset_subsumed:                 4
% 3.24/0.99  sim_fw_subsumed:                        3
% 3.24/0.99  sim_bw_subsumed:                        0
% 3.24/0.99  sim_fw_subsumption_res:                 6
% 3.24/0.99  sim_bw_subsumption_res:                 1
% 3.24/0.99  sim_tautology_del:                      0
% 3.24/0.99  sim_eq_tautology_del:                   2
% 3.24/0.99  sim_eq_res_simp:                        0
% 3.24/0.99  sim_fw_demodulated:                     4
% 3.24/0.99  sim_bw_demodulated:                     0
% 3.24/0.99  sim_light_normalised:                   13
% 3.24/0.99  sim_joinable_taut:                      0
% 3.24/0.99  sim_joinable_simp:                      0
% 3.24/0.99  sim_ac_normalised:                      0
% 3.24/0.99  sim_smt_subsumption:                    0
% 3.24/0.99  
%------------------------------------------------------------------------------
