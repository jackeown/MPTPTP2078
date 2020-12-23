%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:59 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1000)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f26,plain,(
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

fof(f25,plain,(
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

fof(f24,plain,(
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

fof(f23,plain,(
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

fof(f22,plain,
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

fof(f27,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f26,f25,f24,f23,f22])).

fof(f45,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f29,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
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

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f28,plain,(
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
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f35,plain,(
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

fof(f3,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f30,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_13,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_250,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_684,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_250])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_253,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_681,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_262,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
    | ~ m1_pre_topc(X0_47,X2_47)
    | ~ m1_pre_topc(X3_47,X2_47)
    | ~ m1_pre_topc(X3_47,X0_47)
    | v2_struct_0(X2_47)
    | v2_struct_0(X1_47)
    | ~ v2_pre_topc(X1_47)
    | ~ v2_pre_topc(X2_47)
    | ~ l1_pre_topc(X1_47)
    | ~ l1_pre_topc(X2_47)
    | ~ v1_funct_1(X0_48)
    | k2_partfun1(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,u1_struct_0(X3_47)) = k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_672,plain,
    ( k2_partfun1(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,u1_struct_0(X2_47)) = k3_tmap_1(X3_47,X1_47,X0_47,X2_47,X0_48)
    | v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
    | m1_pre_topc(X2_47,X0_47) != iProver_top
    | m1_pre_topc(X0_47,X3_47) != iProver_top
    | m1_pre_topc(X2_47,X3_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X3_47) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | v2_pre_topc(X3_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X3_47) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_262])).

cnf(c_1611,plain,
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
    inference(superposition,[status(thm)],[c_681,c_672])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_26,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_27,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_28,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_33,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_34,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2033,plain,
    ( v2_pre_topc(X1_47) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | m1_pre_topc(X0_47,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1611,c_26,c_27,c_28,c_33,c_34,c_35,c_1000])).

cnf(c_2034,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | m1_pre_topc(X0_47,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_2033])).

cnf(c_2047,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_684,c_2034])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_263,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
    | ~ m1_pre_topc(X2_47,X0_47)
    | v2_struct_0(X1_47)
    | v2_struct_0(X0_47)
    | ~ v2_pre_topc(X1_47)
    | ~ v2_pre_topc(X0_47)
    | ~ l1_pre_topc(X1_47)
    | ~ l1_pre_topc(X0_47)
    | ~ v1_funct_1(X0_48)
    | k2_partfun1(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,u1_struct_0(X2_47)) = k2_tmap_1(X0_47,X1_47,X0_48,X2_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_671,plain,
    ( k2_partfun1(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,u1_struct_0(X2_47)) = k2_tmap_1(X0_47,X1_47,X0_48,X2_47)
    | v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
    | m1_pre_topc(X2_47,X0_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | v2_pre_topc(X0_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_263])).

cnf(c_1298,plain,
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
    inference(superposition,[status(thm)],[c_681,c_671])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_23,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_24,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_25,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1444,plain,
    ( m1_pre_topc(X0_47,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k2_tmap_1(sK0,sK1,sK4,X0_47) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1298,c_23,c_24,c_25,c_26,c_27,c_28,c_33,c_34])).

cnf(c_1445,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k2_tmap_1(sK0,sK1,sK4,X0_47)
    | m1_pre_topc(X0_47,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1444])).

cnf(c_1452,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_684,c_1445])).

cnf(c_2081,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2047,c_1452])).

cnf(c_32,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_44,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_46,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_2367,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2081,c_23,c_24,c_25,c_32,c_46])).

cnf(c_258,plain,
    ( m1_pre_topc(X0_47,X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_676,plain,
    ( m1_pre_topc(X0_47,X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_258])).

cnf(c_2049,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k3_tmap_1(X0_47,sK1,sK0,X0_47,sK4)
    | m1_pre_topc(X0_47,sK0) != iProver_top
    | m1_pre_topc(sK0,X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_pre_topc(X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_676,c_2034])).

cnf(c_2644,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k3_tmap_1(sK0,sK1,sK0,sK0,sK4)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_676,c_2049])).

cnf(c_1538,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_676,c_1445])).

cnf(c_45,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_979,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0_47,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k2_tmap_1(sK0,sK1,sK4,X0_47) ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_981,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_1594,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1538,c_22,c_21,c_20,c_19,c_18,c_17,c_12,c_11,c_10,c_45,c_981])).

cnf(c_2650,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK0,sK4) = k2_tmap_1(sK0,sK1,sK4,sK0)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2644,c_1594])).

cnf(c_3423,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK0,sK4) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2650,c_23,c_24,c_25,c_46])).

cnf(c_6,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_257,plain,
    ( r2_funct_2(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,k3_tmap_1(X2_47,X1_47,X0_47,X0_47,X0_48))
    | ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
    | ~ m1_pre_topc(X0_47,X2_47)
    | v2_struct_0(X1_47)
    | v2_struct_0(X0_47)
    | v2_struct_0(X2_47)
    | ~ v2_pre_topc(X1_47)
    | ~ v2_pre_topc(X2_47)
    | ~ l1_pre_topc(X1_47)
    | ~ l1_pre_topc(X2_47)
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_677,plain,
    ( r2_funct_2(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,k3_tmap_1(X2_47,X1_47,X0_47,X0_47,X0_48)) = iProver_top
    | v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
    | m1_pre_topc(X0_47,X2_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(X2_47) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | v2_pre_topc(X2_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X2_47) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_257])).

cnf(c_3428,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3423,c_677])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3870,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3428,c_23,c_24,c_25,c_26,c_27,c_28,c_33,c_34,c_35,c_46])).

cnf(c_7,plain,
    ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_tmap_1(X3,X1,X4,X0))
    | r2_funct_2(u1_struct_0(X5),u1_struct_0(X1),k3_tmap_1(X3,X1,X0,X5,X2),k2_tmap_1(X3,X1,X4,X5))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X5,X3)
    | ~ m1_pre_topc(X5,X0)
    | ~ m1_pre_topc(X0,X3)
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
    inference(cnf_transformation,[],[f35])).

cnf(c_256,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,k2_tmap_1(X2_47,X1_47,X1_48,X0_47))
    | r2_funct_2(u1_struct_0(X3_47),u1_struct_0(X1_47),k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),k2_tmap_1(X2_47,X1_47,X1_48,X3_47))
    | ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
    | ~ v1_funct_2(X1_48,u1_struct_0(X2_47),u1_struct_0(X1_47))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_47),u1_struct_0(X1_47))))
    | ~ m1_pre_topc(X3_47,X2_47)
    | ~ m1_pre_topc(X3_47,X0_47)
    | ~ m1_pre_topc(X0_47,X2_47)
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
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_678,plain,
    ( r2_funct_2(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,k2_tmap_1(X2_47,X1_47,X1_48,X0_47)) != iProver_top
    | r2_funct_2(u1_struct_0(X3_47),u1_struct_0(X1_47),k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),k2_tmap_1(X2_47,X1_47,X1_48,X3_47)) = iProver_top
    | v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
    | v1_funct_2(X1_48,u1_struct_0(X2_47),u1_struct_0(X1_47)) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_47),u1_struct_0(X1_47)))) != iProver_top
    | m1_pre_topc(X3_47,X0_47) != iProver_top
    | m1_pre_topc(X0_47,X2_47) != iProver_top
    | m1_pre_topc(X3_47,X2_47) != iProver_top
    | v2_struct_0(X3_47) = iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(X2_47) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | v2_pre_topc(X2_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X2_47) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_256])).

cnf(c_3875,plain,
    ( r2_funct_2(u1_struct_0(X0_47),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_47,sK4),k2_tmap_1(sK0,sK1,sK4,X0_47)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_47,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3870,c_678])).

cnf(c_10677,plain,
    ( v2_struct_0(X0_47) = iProver_top
    | r2_funct_2(u1_struct_0(X0_47),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_47,sK4),k2_tmap_1(sK0,sK1,sK4,X0_47)) = iProver_top
    | m1_pre_topc(X0_47,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3875,c_23,c_24,c_25,c_26,c_27,c_28,c_33,c_34,c_35,c_46])).

cnf(c_10678,plain,
    ( r2_funct_2(u1_struct_0(X0_47),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_47,sK4),k2_tmap_1(sK0,sK1,sK4,X0_47)) = iProver_top
    | m1_pre_topc(X0_47,sK0) != iProver_top
    | v2_struct_0(X0_47) = iProver_top ),
    inference(renaming,[status(thm)],[c_10677])).

cnf(c_10687,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2367,c_10678])).

cnf(c_1107,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_47),u1_struct_0(sK1),X0_48,k2_tmap_1(X1_47,sK1,X1_48,X0_47))
    | r2_funct_2(u1_struct_0(X2_47),u1_struct_0(sK1),k3_tmap_1(X1_47,sK1,X0_47,X2_47,X0_48),k2_tmap_1(X1_47,sK1,X1_48,X2_47))
    | ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(sK1))
    | ~ v1_funct_2(X1_48,u1_struct_0(X1_47),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(sK1))))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_47),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X2_47,X0_47)
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ m1_pre_topc(X2_47,X1_47)
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
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_6444,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
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
    inference(instantiation,[status(thm)],[c_1107])).

cnf(c_6445,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6444])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_259,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
    | ~ m1_pre_topc(X0_47,X2_47)
    | ~ m1_pre_topc(X3_47,X2_47)
    | v2_struct_0(X2_47)
    | v2_struct_0(X1_47)
    | ~ v2_pre_topc(X1_47)
    | ~ v2_pre_topc(X2_47)
    | ~ l1_pre_topc(X1_47)
    | ~ l1_pre_topc(X2_47)
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_675,plain,
    ( v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
    | m1_pre_topc(X0_47,X2_47) != iProver_top
    | m1_pre_topc(X3_47,X2_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X2_47) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | v2_pre_topc(X2_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X2_47) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_259])).

cnf(c_1676,plain,
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
    inference(superposition,[status(thm)],[c_681,c_675])).

cnf(c_2020,plain,
    ( v1_funct_1(k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | m1_pre_topc(sK0,X1_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1676,c_26,c_27,c_28,c_33,c_34])).

cnf(c_2021,plain,
    ( m1_pre_topc(X0_47,X1_47) != iProver_top
    | m1_pre_topc(sK0,X1_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2020])).

cnf(c_2372,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2367,c_2021])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_260,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
    | v1_funct_2(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),u1_struct_0(X3_47),u1_struct_0(X1_47))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
    | ~ m1_pre_topc(X3_47,X2_47)
    | ~ m1_pre_topc(X0_47,X2_47)
    | v2_struct_0(X1_47)
    | v2_struct_0(X2_47)
    | ~ v2_pre_topc(X1_47)
    | ~ v2_pre_topc(X2_47)
    | ~ l1_pre_topc(X1_47)
    | ~ l1_pre_topc(X2_47)
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_674,plain,
    ( v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),u1_struct_0(X3_47),u1_struct_0(X1_47)) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
    | m1_pre_topc(X0_47,X2_47) != iProver_top
    | m1_pre_topc(X3_47,X2_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X2_47) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | v2_pre_topc(X2_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X2_47) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_260])).

cnf(c_2371,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2367,c_674])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X3,X2,X1,X4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_261,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
    | m1_subset_1(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_47),u1_struct_0(X1_47))))
    | ~ m1_pre_topc(X3_47,X2_47)
    | ~ m1_pre_topc(X0_47,X2_47)
    | v2_struct_0(X1_47)
    | v2_struct_0(X2_47)
    | ~ v2_pre_topc(X1_47)
    | ~ v2_pre_topc(X2_47)
    | ~ l1_pre_topc(X1_47)
    | ~ l1_pre_topc(X2_47)
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_673,plain,
    ( v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_47),u1_struct_0(X1_47)))) = iProver_top
    | m1_pre_topc(X0_47,X2_47) != iProver_top
    | m1_pre_topc(X3_47,X2_47) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X2_47) = iProver_top
    | v2_pre_topc(X1_47) != iProver_top
    | v2_pre_topc(X2_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(X2_47) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_2370,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2367,c_673])).

cnf(c_8,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_37,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_36,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_14,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_31,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_30,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_29,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10687,c_6445,c_2372,c_2371,c_2370,c_46,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.80/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.02  
% 2.80/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.80/1.02  
% 2.80/1.02  ------  iProver source info
% 2.80/1.02  
% 2.80/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.80/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.80/1.02  git: non_committed_changes: false
% 2.80/1.02  git: last_make_outside_of_git: false
% 2.80/1.02  
% 2.80/1.02  ------ 
% 2.80/1.02  
% 2.80/1.02  ------ Input Options
% 2.80/1.02  
% 2.80/1.02  --out_options                           all
% 2.80/1.02  --tptp_safe_out                         true
% 2.80/1.02  --problem_path                          ""
% 2.80/1.02  --include_path                          ""
% 2.80/1.02  --clausifier                            res/vclausify_rel
% 2.80/1.02  --clausifier_options                    --mode clausify
% 2.80/1.02  --stdin                                 false
% 2.80/1.02  --stats_out                             all
% 2.80/1.02  
% 2.80/1.02  ------ General Options
% 2.80/1.02  
% 2.80/1.02  --fof                                   false
% 2.80/1.02  --time_out_real                         305.
% 2.80/1.02  --time_out_virtual                      -1.
% 2.80/1.02  --symbol_type_check                     false
% 2.80/1.02  --clausify_out                          false
% 2.80/1.02  --sig_cnt_out                           false
% 2.80/1.02  --trig_cnt_out                          false
% 2.80/1.02  --trig_cnt_out_tolerance                1.
% 2.80/1.02  --trig_cnt_out_sk_spl                   false
% 2.80/1.02  --abstr_cl_out                          false
% 2.80/1.02  
% 2.80/1.02  ------ Global Options
% 2.80/1.02  
% 2.80/1.02  --schedule                              default
% 2.80/1.02  --add_important_lit                     false
% 2.80/1.02  --prop_solver_per_cl                    1000
% 2.80/1.02  --min_unsat_core                        false
% 2.80/1.02  --soft_assumptions                      false
% 2.80/1.02  --soft_lemma_size                       3
% 2.80/1.02  --prop_impl_unit_size                   0
% 2.80/1.02  --prop_impl_unit                        []
% 2.80/1.02  --share_sel_clauses                     true
% 2.80/1.02  --reset_solvers                         false
% 2.80/1.02  --bc_imp_inh                            [conj_cone]
% 2.80/1.02  --conj_cone_tolerance                   3.
% 2.80/1.02  --extra_neg_conj                        none
% 2.80/1.02  --large_theory_mode                     true
% 2.80/1.02  --prolific_symb_bound                   200
% 2.80/1.02  --lt_threshold                          2000
% 2.80/1.02  --clause_weak_htbl                      true
% 2.80/1.02  --gc_record_bc_elim                     false
% 2.80/1.02  
% 2.80/1.02  ------ Preprocessing Options
% 2.80/1.02  
% 2.80/1.02  --preprocessing_flag                    true
% 2.80/1.02  --time_out_prep_mult                    0.1
% 2.80/1.02  --splitting_mode                        input
% 2.80/1.02  --splitting_grd                         true
% 2.80/1.02  --splitting_cvd                         false
% 2.80/1.02  --splitting_cvd_svl                     false
% 2.80/1.02  --splitting_nvd                         32
% 2.80/1.02  --sub_typing                            true
% 2.80/1.02  --prep_gs_sim                           true
% 2.80/1.02  --prep_unflatten                        true
% 2.80/1.02  --prep_res_sim                          true
% 2.80/1.02  --prep_upred                            true
% 2.80/1.02  --prep_sem_filter                       exhaustive
% 2.80/1.02  --prep_sem_filter_out                   false
% 2.80/1.02  --pred_elim                             true
% 2.80/1.02  --res_sim_input                         true
% 2.80/1.02  --eq_ax_congr_red                       true
% 2.80/1.02  --pure_diseq_elim                       true
% 2.80/1.02  --brand_transform                       false
% 2.80/1.02  --non_eq_to_eq                          false
% 2.80/1.02  --prep_def_merge                        true
% 2.80/1.02  --prep_def_merge_prop_impl              false
% 2.80/1.02  --prep_def_merge_mbd                    true
% 2.80/1.02  --prep_def_merge_tr_red                 false
% 2.80/1.02  --prep_def_merge_tr_cl                  false
% 2.80/1.02  --smt_preprocessing                     true
% 2.80/1.02  --smt_ac_axioms                         fast
% 2.80/1.02  --preprocessed_out                      false
% 2.80/1.02  --preprocessed_stats                    false
% 2.80/1.02  
% 2.80/1.02  ------ Abstraction refinement Options
% 2.80/1.02  
% 2.80/1.02  --abstr_ref                             []
% 2.80/1.02  --abstr_ref_prep                        false
% 2.80/1.02  --abstr_ref_until_sat                   false
% 2.80/1.02  --abstr_ref_sig_restrict                funpre
% 2.80/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/1.02  --abstr_ref_under                       []
% 2.80/1.02  
% 2.80/1.02  ------ SAT Options
% 2.80/1.02  
% 2.80/1.02  --sat_mode                              false
% 2.80/1.02  --sat_fm_restart_options                ""
% 2.80/1.02  --sat_gr_def                            false
% 2.80/1.02  --sat_epr_types                         true
% 2.80/1.02  --sat_non_cyclic_types                  false
% 2.80/1.02  --sat_finite_models                     false
% 2.80/1.02  --sat_fm_lemmas                         false
% 2.80/1.02  --sat_fm_prep                           false
% 2.80/1.02  --sat_fm_uc_incr                        true
% 2.80/1.02  --sat_out_model                         small
% 2.80/1.02  --sat_out_clauses                       false
% 2.80/1.02  
% 2.80/1.02  ------ QBF Options
% 2.80/1.02  
% 2.80/1.02  --qbf_mode                              false
% 2.80/1.02  --qbf_elim_univ                         false
% 2.80/1.02  --qbf_dom_inst                          none
% 2.80/1.02  --qbf_dom_pre_inst                      false
% 2.80/1.02  --qbf_sk_in                             false
% 2.80/1.02  --qbf_pred_elim                         true
% 2.80/1.02  --qbf_split                             512
% 2.80/1.02  
% 2.80/1.02  ------ BMC1 Options
% 2.80/1.02  
% 2.80/1.02  --bmc1_incremental                      false
% 2.80/1.02  --bmc1_axioms                           reachable_all
% 2.80/1.02  --bmc1_min_bound                        0
% 2.80/1.02  --bmc1_max_bound                        -1
% 2.80/1.02  --bmc1_max_bound_default                -1
% 2.80/1.02  --bmc1_symbol_reachability              true
% 2.80/1.02  --bmc1_property_lemmas                  false
% 2.80/1.02  --bmc1_k_induction                      false
% 2.80/1.02  --bmc1_non_equiv_states                 false
% 2.80/1.02  --bmc1_deadlock                         false
% 2.80/1.02  --bmc1_ucm                              false
% 2.80/1.02  --bmc1_add_unsat_core                   none
% 2.80/1.02  --bmc1_unsat_core_children              false
% 2.80/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/1.02  --bmc1_out_stat                         full
% 2.80/1.02  --bmc1_ground_init                      false
% 2.80/1.02  --bmc1_pre_inst_next_state              false
% 2.80/1.02  --bmc1_pre_inst_state                   false
% 2.80/1.02  --bmc1_pre_inst_reach_state             false
% 2.80/1.02  --bmc1_out_unsat_core                   false
% 2.80/1.02  --bmc1_aig_witness_out                  false
% 2.80/1.02  --bmc1_verbose                          false
% 2.80/1.02  --bmc1_dump_clauses_tptp                false
% 2.80/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.80/1.02  --bmc1_dump_file                        -
% 2.80/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.80/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.80/1.02  --bmc1_ucm_extend_mode                  1
% 2.80/1.02  --bmc1_ucm_init_mode                    2
% 2.80/1.02  --bmc1_ucm_cone_mode                    none
% 2.80/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.80/1.02  --bmc1_ucm_relax_model                  4
% 2.80/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.80/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/1.02  --bmc1_ucm_layered_model                none
% 2.80/1.02  --bmc1_ucm_max_lemma_size               10
% 2.80/1.02  
% 2.80/1.02  ------ AIG Options
% 2.80/1.02  
% 2.80/1.02  --aig_mode                              false
% 2.80/1.02  
% 2.80/1.02  ------ Instantiation Options
% 2.80/1.02  
% 2.80/1.02  --instantiation_flag                    true
% 2.80/1.02  --inst_sos_flag                         false
% 2.80/1.02  --inst_sos_phase                        true
% 2.80/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/1.02  --inst_lit_sel_side                     num_symb
% 2.80/1.02  --inst_solver_per_active                1400
% 2.80/1.02  --inst_solver_calls_frac                1.
% 2.80/1.02  --inst_passive_queue_type               priority_queues
% 2.80/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/1.02  --inst_passive_queues_freq              [25;2]
% 2.80/1.02  --inst_dismatching                      true
% 2.80/1.02  --inst_eager_unprocessed_to_passive     true
% 2.80/1.02  --inst_prop_sim_given                   true
% 2.80/1.02  --inst_prop_sim_new                     false
% 2.80/1.02  --inst_subs_new                         false
% 2.80/1.02  --inst_eq_res_simp                      false
% 2.80/1.02  --inst_subs_given                       false
% 2.80/1.02  --inst_orphan_elimination               true
% 2.80/1.02  --inst_learning_loop_flag               true
% 2.80/1.02  --inst_learning_start                   3000
% 2.80/1.02  --inst_learning_factor                  2
% 2.80/1.02  --inst_start_prop_sim_after_learn       3
% 2.80/1.02  --inst_sel_renew                        solver
% 2.80/1.02  --inst_lit_activity_flag                true
% 2.80/1.02  --inst_restr_to_given                   false
% 2.80/1.02  --inst_activity_threshold               500
% 2.80/1.02  --inst_out_proof                        true
% 2.80/1.02  
% 2.80/1.02  ------ Resolution Options
% 2.80/1.02  
% 2.80/1.02  --resolution_flag                       true
% 2.80/1.02  --res_lit_sel                           adaptive
% 2.80/1.02  --res_lit_sel_side                      none
% 2.80/1.02  --res_ordering                          kbo
% 2.80/1.02  --res_to_prop_solver                    active
% 2.80/1.02  --res_prop_simpl_new                    false
% 2.80/1.02  --res_prop_simpl_given                  true
% 2.80/1.02  --res_passive_queue_type                priority_queues
% 2.80/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/1.02  --res_passive_queues_freq               [15;5]
% 2.80/1.02  --res_forward_subs                      full
% 2.80/1.02  --res_backward_subs                     full
% 2.80/1.02  --res_forward_subs_resolution           true
% 2.80/1.02  --res_backward_subs_resolution          true
% 2.80/1.02  --res_orphan_elimination                true
% 2.80/1.02  --res_time_limit                        2.
% 2.80/1.02  --res_out_proof                         true
% 2.80/1.02  
% 2.80/1.02  ------ Superposition Options
% 2.80/1.02  
% 2.80/1.02  --superposition_flag                    true
% 2.80/1.02  --sup_passive_queue_type                priority_queues
% 2.80/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.80/1.02  --demod_completeness_check              fast
% 2.80/1.02  --demod_use_ground                      true
% 2.80/1.02  --sup_to_prop_solver                    passive
% 2.80/1.02  --sup_prop_simpl_new                    true
% 2.80/1.02  --sup_prop_simpl_given                  true
% 2.80/1.02  --sup_fun_splitting                     false
% 2.80/1.02  --sup_smt_interval                      50000
% 2.80/1.02  
% 2.80/1.02  ------ Superposition Simplification Setup
% 2.80/1.02  
% 2.80/1.02  --sup_indices_passive                   []
% 2.80/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.02  --sup_full_bw                           [BwDemod]
% 2.80/1.02  --sup_immed_triv                        [TrivRules]
% 2.80/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.02  --sup_immed_bw_main                     []
% 2.80/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.02  
% 2.80/1.02  ------ Combination Options
% 2.80/1.02  
% 2.80/1.02  --comb_res_mult                         3
% 2.80/1.02  --comb_sup_mult                         2
% 2.80/1.02  --comb_inst_mult                        10
% 2.80/1.02  
% 2.80/1.02  ------ Debug Options
% 2.80/1.02  
% 2.80/1.02  --dbg_backtrace                         false
% 2.80/1.02  --dbg_dump_prop_clauses                 false
% 2.80/1.02  --dbg_dump_prop_clauses_file            -
% 2.80/1.02  --dbg_out_stat                          false
% 2.80/1.02  ------ Parsing...
% 2.80/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.80/1.02  
% 2.80/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.80/1.02  
% 2.80/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.80/1.02  
% 2.80/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.80/1.02  ------ Proving...
% 2.80/1.02  ------ Problem Properties 
% 2.80/1.02  
% 2.80/1.02  
% 2.80/1.02  clauses                                 23
% 2.80/1.02  conjectures                             15
% 2.80/1.02  EPR                                     13
% 2.80/1.02  Horn                                    16
% 2.80/1.02  unary                                   15
% 2.80/1.02  binary                                  1
% 2.80/1.02  lits                                    108
% 2.80/1.02  lits eq                                 2
% 2.80/1.02  fd_pure                                 0
% 2.80/1.02  fd_pseudo                               0
% 2.80/1.02  fd_cond                                 0
% 2.80/1.02  fd_pseudo_cond                          0
% 2.80/1.02  AC symbols                              0
% 2.80/1.02  
% 2.80/1.02  ------ Schedule dynamic 5 is on 
% 2.80/1.02  
% 2.80/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.80/1.02  
% 2.80/1.02  
% 2.80/1.02  ------ 
% 2.80/1.02  Current options:
% 2.80/1.02  ------ 
% 2.80/1.02  
% 2.80/1.02  ------ Input Options
% 2.80/1.02  
% 2.80/1.02  --out_options                           all
% 2.80/1.02  --tptp_safe_out                         true
% 2.80/1.02  --problem_path                          ""
% 2.80/1.02  --include_path                          ""
% 2.80/1.02  --clausifier                            res/vclausify_rel
% 2.80/1.02  --clausifier_options                    --mode clausify
% 2.80/1.02  --stdin                                 false
% 2.80/1.02  --stats_out                             all
% 2.80/1.02  
% 2.80/1.02  ------ General Options
% 2.80/1.02  
% 2.80/1.02  --fof                                   false
% 2.80/1.02  --time_out_real                         305.
% 2.80/1.02  --time_out_virtual                      -1.
% 2.80/1.02  --symbol_type_check                     false
% 2.80/1.02  --clausify_out                          false
% 2.80/1.02  --sig_cnt_out                           false
% 2.80/1.02  --trig_cnt_out                          false
% 2.80/1.02  --trig_cnt_out_tolerance                1.
% 2.80/1.02  --trig_cnt_out_sk_spl                   false
% 2.80/1.02  --abstr_cl_out                          false
% 2.80/1.02  
% 2.80/1.02  ------ Global Options
% 2.80/1.02  
% 2.80/1.02  --schedule                              default
% 2.80/1.02  --add_important_lit                     false
% 2.80/1.02  --prop_solver_per_cl                    1000
% 2.80/1.02  --min_unsat_core                        false
% 2.80/1.02  --soft_assumptions                      false
% 2.80/1.02  --soft_lemma_size                       3
% 2.80/1.02  --prop_impl_unit_size                   0
% 2.80/1.02  --prop_impl_unit                        []
% 2.80/1.02  --share_sel_clauses                     true
% 2.80/1.02  --reset_solvers                         false
% 2.80/1.02  --bc_imp_inh                            [conj_cone]
% 2.80/1.02  --conj_cone_tolerance                   3.
% 2.80/1.02  --extra_neg_conj                        none
% 2.80/1.02  --large_theory_mode                     true
% 2.80/1.02  --prolific_symb_bound                   200
% 2.80/1.02  --lt_threshold                          2000
% 2.80/1.02  --clause_weak_htbl                      true
% 2.80/1.02  --gc_record_bc_elim                     false
% 2.80/1.02  
% 2.80/1.02  ------ Preprocessing Options
% 2.80/1.02  
% 2.80/1.02  --preprocessing_flag                    true
% 2.80/1.02  --time_out_prep_mult                    0.1
% 2.80/1.02  --splitting_mode                        input
% 2.80/1.02  --splitting_grd                         true
% 2.80/1.02  --splitting_cvd                         false
% 2.80/1.02  --splitting_cvd_svl                     false
% 2.80/1.02  --splitting_nvd                         32
% 2.80/1.02  --sub_typing                            true
% 2.80/1.02  --prep_gs_sim                           true
% 2.80/1.02  --prep_unflatten                        true
% 2.80/1.02  --prep_res_sim                          true
% 2.80/1.02  --prep_upred                            true
% 2.80/1.02  --prep_sem_filter                       exhaustive
% 2.80/1.02  --prep_sem_filter_out                   false
% 2.80/1.02  --pred_elim                             true
% 2.80/1.02  --res_sim_input                         true
% 2.80/1.02  --eq_ax_congr_red                       true
% 2.80/1.02  --pure_diseq_elim                       true
% 2.80/1.02  --brand_transform                       false
% 2.80/1.02  --non_eq_to_eq                          false
% 2.80/1.02  --prep_def_merge                        true
% 2.80/1.02  --prep_def_merge_prop_impl              false
% 2.80/1.02  --prep_def_merge_mbd                    true
% 2.80/1.02  --prep_def_merge_tr_red                 false
% 2.80/1.02  --prep_def_merge_tr_cl                  false
% 2.80/1.02  --smt_preprocessing                     true
% 2.80/1.02  --smt_ac_axioms                         fast
% 2.80/1.02  --preprocessed_out                      false
% 2.80/1.02  --preprocessed_stats                    false
% 2.80/1.02  
% 2.80/1.02  ------ Abstraction refinement Options
% 2.80/1.02  
% 2.80/1.02  --abstr_ref                             []
% 2.80/1.02  --abstr_ref_prep                        false
% 2.80/1.02  --abstr_ref_until_sat                   false
% 2.80/1.02  --abstr_ref_sig_restrict                funpre
% 2.80/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/1.02  --abstr_ref_under                       []
% 2.80/1.02  
% 2.80/1.02  ------ SAT Options
% 2.80/1.02  
% 2.80/1.02  --sat_mode                              false
% 2.80/1.02  --sat_fm_restart_options                ""
% 2.80/1.02  --sat_gr_def                            false
% 2.80/1.02  --sat_epr_types                         true
% 2.80/1.02  --sat_non_cyclic_types                  false
% 2.80/1.02  --sat_finite_models                     false
% 2.80/1.02  --sat_fm_lemmas                         false
% 2.80/1.02  --sat_fm_prep                           false
% 2.80/1.02  --sat_fm_uc_incr                        true
% 2.80/1.02  --sat_out_model                         small
% 2.80/1.02  --sat_out_clauses                       false
% 2.80/1.02  
% 2.80/1.02  ------ QBF Options
% 2.80/1.02  
% 2.80/1.02  --qbf_mode                              false
% 2.80/1.02  --qbf_elim_univ                         false
% 2.80/1.02  --qbf_dom_inst                          none
% 2.80/1.02  --qbf_dom_pre_inst                      false
% 2.80/1.02  --qbf_sk_in                             false
% 2.80/1.02  --qbf_pred_elim                         true
% 2.80/1.02  --qbf_split                             512
% 2.80/1.02  
% 2.80/1.02  ------ BMC1 Options
% 2.80/1.02  
% 2.80/1.02  --bmc1_incremental                      false
% 2.80/1.02  --bmc1_axioms                           reachable_all
% 2.80/1.02  --bmc1_min_bound                        0
% 2.80/1.02  --bmc1_max_bound                        -1
% 2.80/1.02  --bmc1_max_bound_default                -1
% 2.80/1.02  --bmc1_symbol_reachability              true
% 2.80/1.02  --bmc1_property_lemmas                  false
% 2.80/1.02  --bmc1_k_induction                      false
% 2.80/1.02  --bmc1_non_equiv_states                 false
% 2.80/1.02  --bmc1_deadlock                         false
% 2.80/1.02  --bmc1_ucm                              false
% 2.80/1.02  --bmc1_add_unsat_core                   none
% 2.80/1.02  --bmc1_unsat_core_children              false
% 2.80/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/1.02  --bmc1_out_stat                         full
% 2.80/1.02  --bmc1_ground_init                      false
% 2.80/1.02  --bmc1_pre_inst_next_state              false
% 2.80/1.02  --bmc1_pre_inst_state                   false
% 2.80/1.02  --bmc1_pre_inst_reach_state             false
% 2.80/1.02  --bmc1_out_unsat_core                   false
% 2.80/1.02  --bmc1_aig_witness_out                  false
% 2.80/1.02  --bmc1_verbose                          false
% 2.80/1.02  --bmc1_dump_clauses_tptp                false
% 2.80/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.80/1.02  --bmc1_dump_file                        -
% 2.80/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.80/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.80/1.02  --bmc1_ucm_extend_mode                  1
% 2.80/1.02  --bmc1_ucm_init_mode                    2
% 2.80/1.02  --bmc1_ucm_cone_mode                    none
% 2.80/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.80/1.02  --bmc1_ucm_relax_model                  4
% 2.80/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.80/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/1.02  --bmc1_ucm_layered_model                none
% 2.80/1.02  --bmc1_ucm_max_lemma_size               10
% 2.80/1.02  
% 2.80/1.02  ------ AIG Options
% 2.80/1.02  
% 2.80/1.02  --aig_mode                              false
% 2.80/1.02  
% 2.80/1.02  ------ Instantiation Options
% 2.80/1.02  
% 2.80/1.02  --instantiation_flag                    true
% 2.80/1.02  --inst_sos_flag                         false
% 2.80/1.02  --inst_sos_phase                        true
% 2.80/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/1.02  --inst_lit_sel_side                     none
% 2.80/1.02  --inst_solver_per_active                1400
% 2.80/1.02  --inst_solver_calls_frac                1.
% 2.80/1.02  --inst_passive_queue_type               priority_queues
% 2.80/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/1.02  --inst_passive_queues_freq              [25;2]
% 2.80/1.02  --inst_dismatching                      true
% 2.80/1.02  --inst_eager_unprocessed_to_passive     true
% 2.80/1.02  --inst_prop_sim_given                   true
% 2.80/1.02  --inst_prop_sim_new                     false
% 2.80/1.02  --inst_subs_new                         false
% 2.80/1.02  --inst_eq_res_simp                      false
% 2.80/1.02  --inst_subs_given                       false
% 2.80/1.02  --inst_orphan_elimination               true
% 2.80/1.02  --inst_learning_loop_flag               true
% 2.80/1.02  --inst_learning_start                   3000
% 2.80/1.02  --inst_learning_factor                  2
% 2.80/1.02  --inst_start_prop_sim_after_learn       3
% 2.80/1.02  --inst_sel_renew                        solver
% 2.80/1.02  --inst_lit_activity_flag                true
% 2.80/1.02  --inst_restr_to_given                   false
% 2.80/1.02  --inst_activity_threshold               500
% 2.80/1.02  --inst_out_proof                        true
% 2.80/1.02  
% 2.80/1.02  ------ Resolution Options
% 2.80/1.02  
% 2.80/1.02  --resolution_flag                       false
% 2.80/1.02  --res_lit_sel                           adaptive
% 2.80/1.02  --res_lit_sel_side                      none
% 2.80/1.02  --res_ordering                          kbo
% 2.80/1.02  --res_to_prop_solver                    active
% 2.80/1.02  --res_prop_simpl_new                    false
% 2.80/1.02  --res_prop_simpl_given                  true
% 2.80/1.02  --res_passive_queue_type                priority_queues
% 2.80/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/1.02  --res_passive_queues_freq               [15;5]
% 2.80/1.02  --res_forward_subs                      full
% 2.80/1.02  --res_backward_subs                     full
% 2.80/1.02  --res_forward_subs_resolution           true
% 2.80/1.02  --res_backward_subs_resolution          true
% 2.80/1.02  --res_orphan_elimination                true
% 2.80/1.02  --res_time_limit                        2.
% 2.80/1.02  --res_out_proof                         true
% 2.80/1.02  
% 2.80/1.02  ------ Superposition Options
% 2.80/1.02  
% 2.80/1.02  --superposition_flag                    true
% 2.80/1.02  --sup_passive_queue_type                priority_queues
% 2.80/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.80/1.02  --demod_completeness_check              fast
% 2.80/1.02  --demod_use_ground                      true
% 2.80/1.02  --sup_to_prop_solver                    passive
% 2.80/1.02  --sup_prop_simpl_new                    true
% 2.80/1.02  --sup_prop_simpl_given                  true
% 2.80/1.02  --sup_fun_splitting                     false
% 2.80/1.02  --sup_smt_interval                      50000
% 2.80/1.02  
% 2.80/1.02  ------ Superposition Simplification Setup
% 2.80/1.02  
% 2.80/1.02  --sup_indices_passive                   []
% 2.80/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.02  --sup_full_bw                           [BwDemod]
% 2.80/1.02  --sup_immed_triv                        [TrivRules]
% 2.80/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.02  --sup_immed_bw_main                     []
% 2.80/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.02  
% 2.80/1.02  ------ Combination Options
% 2.80/1.02  
% 2.80/1.02  --comb_res_mult                         3
% 2.80/1.02  --comb_sup_mult                         2
% 2.80/1.02  --comb_inst_mult                        10
% 2.80/1.02  
% 2.80/1.02  ------ Debug Options
% 2.80/1.02  
% 2.80/1.02  --dbg_backtrace                         false
% 2.80/1.02  --dbg_dump_prop_clauses                 false
% 2.80/1.02  --dbg_dump_prop_clauses_file            -
% 2.80/1.02  --dbg_out_stat                          false
% 2.80/1.02  
% 2.80/1.02  
% 2.80/1.02  
% 2.80/1.02  
% 2.80/1.02  ------ Proving...
% 2.80/1.02  
% 2.80/1.02  
% 2.80/1.02  % SZS status Theorem for theBenchmark.p
% 2.80/1.02  
% 2.80/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.80/1.02  
% 2.80/1.02  fof(f7,conjecture,(
% 2.80/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 2.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f8,negated_conjecture,(
% 2.80/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 2.80/1.02    inference(negated_conjecture,[],[f7])).
% 2.80/1.02  
% 2.80/1.02  fof(f20,plain,(
% 2.80/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.80/1.02    inference(ennf_transformation,[],[f8])).
% 2.80/1.02  
% 2.80/1.02  fof(f21,plain,(
% 2.80/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.80/1.02    inference(flattening,[],[f20])).
% 2.80/1.02  
% 2.80/1.02  fof(f26,plain,(
% 2.80/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,sK4,X3)),k2_tmap_1(X0,X1,sK4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.80/1.02    introduced(choice_axiom,[])).
% 2.80/1.02  
% 2.80/1.02  fof(f25,plain,(
% 2.80/1.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,k2_tmap_1(X0,X1,X4,sK3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.80/1.02    introduced(choice_axiom,[])).
% 2.80/1.02  
% 2.80/1.02  fof(f24,plain,(
% 2.80/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,sK2)) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.80/1.02    introduced(choice_axiom,[])).
% 2.80/1.02  
% 2.80/1.02  fof(f23,plain,(
% 2.80/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,k2_tmap_1(X0,sK1,X4,X3)),k2_tmap_1(X0,sK1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.80/1.02    introduced(choice_axiom,[])).
% 2.80/1.02  
% 2.80/1.02  fof(f22,plain,(
% 2.80/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,k2_tmap_1(sK0,X1,X4,X3)),k2_tmap_1(sK0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.80/1.02    introduced(choice_axiom,[])).
% 2.80/1.02  
% 2.80/1.02  fof(f27,plain,(
% 2.80/1.02    ((((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.80/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f26,f25,f24,f23,f22])).
% 2.80/1.02  
% 2.80/1.02  fof(f45,plain,(
% 2.80/1.02    m1_pre_topc(sK3,sK0)),
% 2.80/1.02    inference(cnf_transformation,[],[f27])).
% 2.80/1.02  
% 2.80/1.02  fof(f48,plain,(
% 2.80/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.80/1.02    inference(cnf_transformation,[],[f27])).
% 2.80/1.02  
% 2.80/1.02  fof(f2,axiom,(
% 2.80/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f11,plain,(
% 2.80/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.80/1.02    inference(ennf_transformation,[],[f2])).
% 2.80/1.02  
% 2.80/1.02  fof(f12,plain,(
% 2.80/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.80/1.02    inference(flattening,[],[f11])).
% 2.80/1.02  
% 2.80/1.02  fof(f29,plain,(
% 2.80/1.02    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.80/1.02    inference(cnf_transformation,[],[f12])).
% 2.80/1.02  
% 2.80/1.02  fof(f39,plain,(
% 2.80/1.02    ~v2_struct_0(sK1)),
% 2.80/1.02    inference(cnf_transformation,[],[f27])).
% 2.80/1.02  
% 2.80/1.02  fof(f40,plain,(
% 2.80/1.02    v2_pre_topc(sK1)),
% 2.80/1.02    inference(cnf_transformation,[],[f27])).
% 2.80/1.02  
% 2.80/1.02  fof(f41,plain,(
% 2.80/1.02    l1_pre_topc(sK1)),
% 2.80/1.02    inference(cnf_transformation,[],[f27])).
% 2.80/1.02  
% 2.80/1.02  fof(f46,plain,(
% 2.80/1.02    v1_funct_1(sK4)),
% 2.80/1.02    inference(cnf_transformation,[],[f27])).
% 2.80/1.02  
% 2.80/1.02  fof(f47,plain,(
% 2.80/1.02    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.80/1.02    inference(cnf_transformation,[],[f27])).
% 2.80/1.02  
% 2.80/1.02  fof(f1,axiom,(
% 2.80/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f9,plain,(
% 2.80/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.80/1.02    inference(ennf_transformation,[],[f1])).
% 2.80/1.02  
% 2.80/1.02  fof(f10,plain,(
% 2.80/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.80/1.02    inference(flattening,[],[f9])).
% 2.80/1.02  
% 2.80/1.02  fof(f28,plain,(
% 2.80/1.02    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.80/1.02    inference(cnf_transformation,[],[f10])).
% 2.80/1.02  
% 2.80/1.02  fof(f36,plain,(
% 2.80/1.02    ~v2_struct_0(sK0)),
% 2.80/1.02    inference(cnf_transformation,[],[f27])).
% 2.80/1.02  
% 2.80/1.02  fof(f37,plain,(
% 2.80/1.02    v2_pre_topc(sK0)),
% 2.80/1.02    inference(cnf_transformation,[],[f27])).
% 2.80/1.02  
% 2.80/1.02  fof(f38,plain,(
% 2.80/1.02    l1_pre_topc(sK0)),
% 2.80/1.02    inference(cnf_transformation,[],[f27])).
% 2.80/1.02  
% 2.80/1.02  fof(f4,axiom,(
% 2.80/1.02    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f15,plain,(
% 2.80/1.02    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.80/1.02    inference(ennf_transformation,[],[f4])).
% 2.80/1.02  
% 2.80/1.02  fof(f33,plain,(
% 2.80/1.02    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.80/1.02    inference(cnf_transformation,[],[f15])).
% 2.80/1.02  
% 2.80/1.02  fof(f5,axiom,(
% 2.80/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 2.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f16,plain,(
% 2.80/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.80/1.02    inference(ennf_transformation,[],[f5])).
% 2.80/1.02  
% 2.80/1.02  fof(f17,plain,(
% 2.80/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.80/1.02    inference(flattening,[],[f16])).
% 2.80/1.02  
% 2.80/1.02  fof(f34,plain,(
% 2.80/1.02    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.80/1.02    inference(cnf_transformation,[],[f17])).
% 2.80/1.02  
% 2.80/1.02  fof(f6,axiom,(
% 2.80/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_pre_topc(X3,X2) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))) => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 2.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f18,plain,(
% 2.80/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | (~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.80/1.02    inference(ennf_transformation,[],[f6])).
% 2.80/1.02  
% 2.80/1.02  fof(f19,plain,(
% 2.80/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.80/1.02    inference(flattening,[],[f18])).
% 2.80/1.02  
% 2.80/1.02  fof(f35,plain,(
% 2.80/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.80/1.02    inference(cnf_transformation,[],[f19])).
% 2.80/1.02  
% 2.80/1.02  fof(f3,axiom,(
% 2.80/1.02    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 2.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/1.02  
% 2.80/1.02  fof(f13,plain,(
% 2.80/1.02    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.80/1.02    inference(ennf_transformation,[],[f3])).
% 2.80/1.02  
% 2.80/1.02  fof(f14,plain,(
% 2.80/1.02    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.80/1.02    inference(flattening,[],[f13])).
% 2.80/1.02  
% 2.80/1.02  fof(f30,plain,(
% 2.80/1.02    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.80/1.02    inference(cnf_transformation,[],[f14])).
% 2.80/1.02  
% 2.80/1.02  fof(f31,plain,(
% 2.80/1.02    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.80/1.02    inference(cnf_transformation,[],[f14])).
% 2.80/1.02  
% 2.80/1.02  fof(f32,plain,(
% 2.80/1.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.80/1.02    inference(cnf_transformation,[],[f14])).
% 2.80/1.02  
% 2.80/1.02  fof(f50,plain,(
% 2.80/1.02    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))),
% 2.80/1.02    inference(cnf_transformation,[],[f27])).
% 2.80/1.02  
% 2.80/1.02  fof(f49,plain,(
% 2.80/1.02    m1_pre_topc(sK2,sK3)),
% 2.80/1.02    inference(cnf_transformation,[],[f27])).
% 2.80/1.02  
% 2.80/1.02  fof(f44,plain,(
% 2.80/1.02    ~v2_struct_0(sK3)),
% 2.80/1.02    inference(cnf_transformation,[],[f27])).
% 2.80/1.02  
% 2.80/1.02  fof(f43,plain,(
% 2.80/1.02    m1_pre_topc(sK2,sK0)),
% 2.80/1.02    inference(cnf_transformation,[],[f27])).
% 2.80/1.02  
% 2.80/1.02  fof(f42,plain,(
% 2.80/1.02    ~v2_struct_0(sK2)),
% 2.80/1.02    inference(cnf_transformation,[],[f27])).
% 2.80/1.02  
% 2.80/1.02  cnf(c_13,negated_conjecture,
% 2.80/1.02      ( m1_pre_topc(sK3,sK0) ),
% 2.80/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_250,negated_conjecture,
% 2.80/1.02      ( m1_pre_topc(sK3,sK0) ),
% 2.80/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_684,plain,
% 2.80/1.02      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_250]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_10,negated_conjecture,
% 2.80/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.80/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_253,negated_conjecture,
% 2.80/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.80/1.02      inference(subtyping,[status(esa)],[c_10]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_681,plain,
% 2.80/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_253]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_1,plain,
% 2.80/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.80/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.80/1.02      | ~ m1_pre_topc(X3,X4)
% 2.80/1.02      | ~ m1_pre_topc(X3,X1)
% 2.80/1.02      | ~ m1_pre_topc(X1,X4)
% 2.80/1.02      | v2_struct_0(X4)
% 2.80/1.02      | v2_struct_0(X2)
% 2.80/1.02      | ~ v2_pre_topc(X2)
% 2.80/1.02      | ~ v2_pre_topc(X4)
% 2.80/1.02      | ~ l1_pre_topc(X2)
% 2.80/1.02      | ~ l1_pre_topc(X4)
% 2.80/1.02      | ~ v1_funct_1(X0)
% 2.80/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.80/1.02      inference(cnf_transformation,[],[f29]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_262,plain,
% 2.80/1.02      ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
% 2.80/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
% 2.80/1.02      | ~ m1_pre_topc(X0_47,X2_47)
% 2.80/1.02      | ~ m1_pre_topc(X3_47,X2_47)
% 2.80/1.02      | ~ m1_pre_topc(X3_47,X0_47)
% 2.80/1.02      | v2_struct_0(X2_47)
% 2.80/1.02      | v2_struct_0(X1_47)
% 2.80/1.02      | ~ v2_pre_topc(X1_47)
% 2.80/1.02      | ~ v2_pre_topc(X2_47)
% 2.80/1.02      | ~ l1_pre_topc(X1_47)
% 2.80/1.02      | ~ l1_pre_topc(X2_47)
% 2.80/1.02      | ~ v1_funct_1(X0_48)
% 2.80/1.02      | k2_partfun1(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,u1_struct_0(X3_47)) = k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48) ),
% 2.80/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_672,plain,
% 2.80/1.02      ( k2_partfun1(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,u1_struct_0(X2_47)) = k3_tmap_1(X3_47,X1_47,X0_47,X2_47,X0_48)
% 2.80/1.02      | v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
% 2.80/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
% 2.80/1.02      | m1_pre_topc(X2_47,X0_47) != iProver_top
% 2.80/1.02      | m1_pre_topc(X0_47,X3_47) != iProver_top
% 2.80/1.02      | m1_pre_topc(X2_47,X3_47) != iProver_top
% 2.80/1.02      | v2_struct_0(X1_47) = iProver_top
% 2.80/1.02      | v2_struct_0(X3_47) = iProver_top
% 2.80/1.02      | v2_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | v2_pre_topc(X3_47) != iProver_top
% 2.80/1.02      | l1_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | l1_pre_topc(X3_47) != iProver_top
% 2.80/1.02      | v1_funct_1(X0_48) != iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_262]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_1611,plain,
% 2.80/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)
% 2.80/1.02      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.80/1.02      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.80/1.02      | m1_pre_topc(X0_47,sK0) != iProver_top
% 2.80/1.02      | m1_pre_topc(sK0,X1_47) != iProver_top
% 2.80/1.02      | v2_struct_0(X1_47) = iProver_top
% 2.80/1.02      | v2_struct_0(sK1) = iProver_top
% 2.80/1.02      | v2_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | v2_pre_topc(sK1) != iProver_top
% 2.80/1.02      | l1_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.80/1.02      | v1_funct_1(sK4) != iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_681,c_672]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_19,negated_conjecture,
% 2.80/1.02      ( ~ v2_struct_0(sK1) ),
% 2.80/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_26,plain,
% 2.80/1.02      ( v2_struct_0(sK1) != iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_18,negated_conjecture,
% 2.80/1.02      ( v2_pre_topc(sK1) ),
% 2.80/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_27,plain,
% 2.80/1.02      ( v2_pre_topc(sK1) = iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_17,negated_conjecture,
% 2.80/1.02      ( l1_pre_topc(sK1) ),
% 2.80/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_28,plain,
% 2.80/1.02      ( l1_pre_topc(sK1) = iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_12,negated_conjecture,
% 2.80/1.02      ( v1_funct_1(sK4) ),
% 2.80/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_33,plain,
% 2.80/1.02      ( v1_funct_1(sK4) = iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_11,negated_conjecture,
% 2.80/1.02      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.80/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_34,plain,
% 2.80/1.02      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2033,plain,
% 2.80/1.02      ( v2_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)
% 2.80/1.02      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.80/1.02      | m1_pre_topc(X0_47,sK0) != iProver_top
% 2.80/1.02      | m1_pre_topc(sK0,X1_47) != iProver_top
% 2.80/1.02      | v2_struct_0(X1_47) = iProver_top
% 2.80/1.02      | l1_pre_topc(X1_47) != iProver_top ),
% 2.80/1.02      inference(global_propositional_subsumption,
% 2.80/1.02                [status(thm)],
% 2.80/1.02                [c_1611,c_26,c_27,c_28,c_33,c_34,c_35,c_1000]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2034,plain,
% 2.80/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)
% 2.80/1.02      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.80/1.02      | m1_pre_topc(X0_47,sK0) != iProver_top
% 2.80/1.02      | m1_pre_topc(sK0,X1_47) != iProver_top
% 2.80/1.02      | v2_struct_0(X1_47) = iProver_top
% 2.80/1.02      | v2_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | l1_pre_topc(X1_47) != iProver_top ),
% 2.80/1.02      inference(renaming,[status(thm)],[c_2033]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2047,plain,
% 2.80/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
% 2.80/1.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.80/1.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.80/1.02      | v2_struct_0(sK0) = iProver_top
% 2.80/1.02      | v2_pre_topc(sK0) != iProver_top
% 2.80/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_684,c_2034]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_0,plain,
% 2.80/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.80/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.80/1.02      | ~ m1_pre_topc(X3,X1)
% 2.80/1.02      | v2_struct_0(X1)
% 2.80/1.02      | v2_struct_0(X2)
% 2.80/1.02      | ~ v2_pre_topc(X2)
% 2.80/1.02      | ~ v2_pre_topc(X1)
% 2.80/1.02      | ~ l1_pre_topc(X2)
% 2.80/1.02      | ~ l1_pre_topc(X1)
% 2.80/1.02      | ~ v1_funct_1(X0)
% 2.80/1.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.80/1.02      inference(cnf_transformation,[],[f28]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_263,plain,
% 2.80/1.02      ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
% 2.80/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
% 2.80/1.02      | ~ m1_pre_topc(X2_47,X0_47)
% 2.80/1.02      | v2_struct_0(X1_47)
% 2.80/1.02      | v2_struct_0(X0_47)
% 2.80/1.02      | ~ v2_pre_topc(X1_47)
% 2.80/1.02      | ~ v2_pre_topc(X0_47)
% 2.80/1.02      | ~ l1_pre_topc(X1_47)
% 2.80/1.02      | ~ l1_pre_topc(X0_47)
% 2.80/1.02      | ~ v1_funct_1(X0_48)
% 2.80/1.02      | k2_partfun1(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,u1_struct_0(X2_47)) = k2_tmap_1(X0_47,X1_47,X0_48,X2_47) ),
% 2.80/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_671,plain,
% 2.80/1.02      ( k2_partfun1(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,u1_struct_0(X2_47)) = k2_tmap_1(X0_47,X1_47,X0_48,X2_47)
% 2.80/1.02      | v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
% 2.80/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
% 2.80/1.02      | m1_pre_topc(X2_47,X0_47) != iProver_top
% 2.80/1.02      | v2_struct_0(X1_47) = iProver_top
% 2.80/1.02      | v2_struct_0(X0_47) = iProver_top
% 2.80/1.02      | v2_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | v2_pre_topc(X0_47) != iProver_top
% 2.80/1.02      | l1_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | l1_pre_topc(X0_47) != iProver_top
% 2.80/1.02      | v1_funct_1(X0_48) != iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_263]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_1298,plain,
% 2.80/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k2_tmap_1(sK0,sK1,sK4,X0_47)
% 2.80/1.02      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.80/1.02      | m1_pre_topc(X0_47,sK0) != iProver_top
% 2.80/1.02      | v2_struct_0(sK0) = iProver_top
% 2.80/1.02      | v2_struct_0(sK1) = iProver_top
% 2.80/1.02      | v2_pre_topc(sK0) != iProver_top
% 2.80/1.02      | v2_pre_topc(sK1) != iProver_top
% 2.80/1.02      | l1_pre_topc(sK0) != iProver_top
% 2.80/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.80/1.02      | v1_funct_1(sK4) != iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_681,c_671]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_22,negated_conjecture,
% 2.80/1.02      ( ~ v2_struct_0(sK0) ),
% 2.80/1.02      inference(cnf_transformation,[],[f36]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_23,plain,
% 2.80/1.02      ( v2_struct_0(sK0) != iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_21,negated_conjecture,
% 2.80/1.02      ( v2_pre_topc(sK0) ),
% 2.80/1.02      inference(cnf_transformation,[],[f37]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_24,plain,
% 2.80/1.02      ( v2_pre_topc(sK0) = iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_20,negated_conjecture,
% 2.80/1.02      ( l1_pre_topc(sK0) ),
% 2.80/1.02      inference(cnf_transformation,[],[f38]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_25,plain,
% 2.80/1.02      ( l1_pre_topc(sK0) = iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_1444,plain,
% 2.80/1.02      ( m1_pre_topc(X0_47,sK0) != iProver_top
% 2.80/1.02      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k2_tmap_1(sK0,sK1,sK4,X0_47) ),
% 2.80/1.02      inference(global_propositional_subsumption,
% 2.80/1.02                [status(thm)],
% 2.80/1.02                [c_1298,c_23,c_24,c_25,c_26,c_27,c_28,c_33,c_34]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_1445,plain,
% 2.80/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k2_tmap_1(sK0,sK1,sK4,X0_47)
% 2.80/1.02      | m1_pre_topc(X0_47,sK0) != iProver_top ),
% 2.80/1.02      inference(renaming,[status(thm)],[c_1444]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_1452,plain,
% 2.80/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_684,c_1445]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2081,plain,
% 2.80/1.02      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
% 2.80/1.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.80/1.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.80/1.02      | v2_struct_0(sK0) = iProver_top
% 2.80/1.02      | v2_pre_topc(sK0) != iProver_top
% 2.80/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 2.80/1.02      inference(light_normalisation,[status(thm)],[c_2047,c_1452]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_32,plain,
% 2.80/1.02      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_5,plain,
% 2.80/1.02      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.80/1.02      inference(cnf_transformation,[],[f33]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_44,plain,
% 2.80/1.02      ( m1_pre_topc(X0,X0) = iProver_top
% 2.80/1.02      | l1_pre_topc(X0) != iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_46,plain,
% 2.80/1.02      ( m1_pre_topc(sK0,sK0) = iProver_top
% 2.80/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 2.80/1.02      inference(instantiation,[status(thm)],[c_44]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2367,plain,
% 2.80/1.02      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 2.80/1.02      inference(global_propositional_subsumption,
% 2.80/1.02                [status(thm)],
% 2.80/1.02                [c_2081,c_23,c_24,c_25,c_32,c_46]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_258,plain,
% 2.80/1.02      ( m1_pre_topc(X0_47,X0_47) | ~ l1_pre_topc(X0_47) ),
% 2.80/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_676,plain,
% 2.80/1.02      ( m1_pre_topc(X0_47,X0_47) = iProver_top
% 2.80/1.02      | l1_pre_topc(X0_47) != iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_258]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2049,plain,
% 2.80/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k3_tmap_1(X0_47,sK1,sK0,X0_47,sK4)
% 2.80/1.02      | m1_pre_topc(X0_47,sK0) != iProver_top
% 2.80/1.02      | m1_pre_topc(sK0,X0_47) != iProver_top
% 2.80/1.02      | v2_struct_0(X0_47) = iProver_top
% 2.80/1.02      | v2_pre_topc(X0_47) != iProver_top
% 2.80/1.02      | l1_pre_topc(X0_47) != iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_676,c_2034]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2644,plain,
% 2.80/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k3_tmap_1(sK0,sK1,sK0,sK0,sK4)
% 2.80/1.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.80/1.02      | v2_struct_0(sK0) = iProver_top
% 2.80/1.02      | v2_pre_topc(sK0) != iProver_top
% 2.80/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_676,c_2049]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_1538,plain,
% 2.80/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0)
% 2.80/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_676,c_1445]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_45,plain,
% 2.80/1.02      ( m1_pre_topc(sK0,sK0) | ~ l1_pre_topc(sK0) ),
% 2.80/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_979,plain,
% 2.80/1.02      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.80/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.80/1.02      | ~ m1_pre_topc(X0_47,sK0)
% 2.80/1.02      | v2_struct_0(sK0)
% 2.80/1.02      | v2_struct_0(sK1)
% 2.80/1.02      | ~ v2_pre_topc(sK0)
% 2.80/1.02      | ~ v2_pre_topc(sK1)
% 2.80/1.02      | ~ l1_pre_topc(sK0)
% 2.80/1.02      | ~ l1_pre_topc(sK1)
% 2.80/1.02      | ~ v1_funct_1(sK4)
% 2.80/1.02      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_47)) = k2_tmap_1(sK0,sK1,sK4,X0_47) ),
% 2.80/1.02      inference(instantiation,[status(thm)],[c_263]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_981,plain,
% 2.80/1.02      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.80/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.80/1.02      | ~ m1_pre_topc(sK0,sK0)
% 2.80/1.02      | v2_struct_0(sK0)
% 2.80/1.02      | v2_struct_0(sK1)
% 2.80/1.02      | ~ v2_pre_topc(sK0)
% 2.80/1.02      | ~ v2_pre_topc(sK1)
% 2.80/1.02      | ~ l1_pre_topc(sK0)
% 2.80/1.02      | ~ l1_pre_topc(sK1)
% 2.80/1.02      | ~ v1_funct_1(sK4)
% 2.80/1.02      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
% 2.80/1.02      inference(instantiation,[status(thm)],[c_979]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_1594,plain,
% 2.80/1.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
% 2.80/1.02      inference(global_propositional_subsumption,
% 2.80/1.02                [status(thm)],
% 2.80/1.02                [c_1538,c_22,c_21,c_20,c_19,c_18,c_17,c_12,c_11,c_10,
% 2.80/1.02                 c_45,c_981]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2650,plain,
% 2.80/1.02      ( k3_tmap_1(sK0,sK1,sK0,sK0,sK4) = k2_tmap_1(sK0,sK1,sK4,sK0)
% 2.80/1.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.80/1.02      | v2_struct_0(sK0) = iProver_top
% 2.80/1.02      | v2_pre_topc(sK0) != iProver_top
% 2.80/1.02      | l1_pre_topc(sK0) != iProver_top ),
% 2.80/1.02      inference(light_normalisation,[status(thm)],[c_2644,c_1594]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_3423,plain,
% 2.80/1.02      ( k3_tmap_1(sK0,sK1,sK0,sK0,sK4) = k2_tmap_1(sK0,sK1,sK4,sK0) ),
% 2.80/1.02      inference(global_propositional_subsumption,
% 2.80/1.02                [status(thm)],
% 2.80/1.02                [c_2650,c_23,c_24,c_25,c_46]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_6,plain,
% 2.80/1.02      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
% 2.80/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.80/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.80/1.02      | ~ m1_pre_topc(X0,X3)
% 2.80/1.02      | v2_struct_0(X3)
% 2.80/1.02      | v2_struct_0(X1)
% 2.80/1.02      | v2_struct_0(X0)
% 2.80/1.02      | ~ v2_pre_topc(X1)
% 2.80/1.02      | ~ v2_pre_topc(X3)
% 2.80/1.02      | ~ l1_pre_topc(X1)
% 2.80/1.02      | ~ l1_pre_topc(X3)
% 2.80/1.02      | ~ v1_funct_1(X2) ),
% 2.80/1.02      inference(cnf_transformation,[],[f34]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_257,plain,
% 2.80/1.02      ( r2_funct_2(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,k3_tmap_1(X2_47,X1_47,X0_47,X0_47,X0_48))
% 2.80/1.02      | ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
% 2.80/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
% 2.80/1.02      | ~ m1_pre_topc(X0_47,X2_47)
% 2.80/1.02      | v2_struct_0(X1_47)
% 2.80/1.02      | v2_struct_0(X0_47)
% 2.80/1.02      | v2_struct_0(X2_47)
% 2.80/1.02      | ~ v2_pre_topc(X1_47)
% 2.80/1.02      | ~ v2_pre_topc(X2_47)
% 2.80/1.02      | ~ l1_pre_topc(X1_47)
% 2.80/1.02      | ~ l1_pre_topc(X2_47)
% 2.80/1.02      | ~ v1_funct_1(X0_48) ),
% 2.80/1.02      inference(subtyping,[status(esa)],[c_6]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_677,plain,
% 2.80/1.02      ( r2_funct_2(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,k3_tmap_1(X2_47,X1_47,X0_47,X0_47,X0_48)) = iProver_top
% 2.80/1.02      | v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
% 2.80/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
% 2.80/1.02      | m1_pre_topc(X0_47,X2_47) != iProver_top
% 2.80/1.02      | v2_struct_0(X1_47) = iProver_top
% 2.80/1.02      | v2_struct_0(X0_47) = iProver_top
% 2.80/1.02      | v2_struct_0(X2_47) = iProver_top
% 2.80/1.02      | v2_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | v2_pre_topc(X2_47) != iProver_top
% 2.80/1.02      | l1_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | l1_pre_topc(X2_47) != iProver_top
% 2.80/1.02      | v1_funct_1(X0_48) != iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_257]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_3428,plain,
% 2.80/1.02      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) = iProver_top
% 2.80/1.02      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.80/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.80/1.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.80/1.02      | v2_struct_0(sK0) = iProver_top
% 2.80/1.02      | v2_struct_0(sK1) = iProver_top
% 2.80/1.02      | v2_pre_topc(sK0) != iProver_top
% 2.80/1.02      | v2_pre_topc(sK1) != iProver_top
% 2.80/1.02      | l1_pre_topc(sK0) != iProver_top
% 2.80/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.80/1.02      | v1_funct_1(sK4) != iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_3423,c_677]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_35,plain,
% 2.80/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_3870,plain,
% 2.80/1.02      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_tmap_1(sK0,sK1,sK4,sK0)) = iProver_top ),
% 2.80/1.02      inference(global_propositional_subsumption,
% 2.80/1.02                [status(thm)],
% 2.80/1.02                [c_3428,c_23,c_24,c_25,c_26,c_27,c_28,c_33,c_34,c_35,
% 2.80/1.02                 c_46]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_7,plain,
% 2.80/1.02      ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_tmap_1(X3,X1,X4,X0))
% 2.80/1.02      | r2_funct_2(u1_struct_0(X5),u1_struct_0(X1),k3_tmap_1(X3,X1,X0,X5,X2),k2_tmap_1(X3,X1,X4,X5))
% 2.80/1.02      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.80/1.02      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
% 2.80/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.80/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.80/1.02      | ~ m1_pre_topc(X5,X3)
% 2.80/1.02      | ~ m1_pre_topc(X5,X0)
% 2.80/1.02      | ~ m1_pre_topc(X0,X3)
% 2.80/1.02      | v2_struct_0(X3)
% 2.80/1.02      | v2_struct_0(X1)
% 2.80/1.02      | v2_struct_0(X0)
% 2.80/1.02      | v2_struct_0(X5)
% 2.80/1.02      | ~ v2_pre_topc(X1)
% 2.80/1.02      | ~ v2_pre_topc(X3)
% 2.80/1.02      | ~ l1_pre_topc(X1)
% 2.80/1.02      | ~ l1_pre_topc(X3)
% 2.80/1.02      | ~ v1_funct_1(X4)
% 2.80/1.02      | ~ v1_funct_1(X2) ),
% 2.80/1.02      inference(cnf_transformation,[],[f35]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_256,plain,
% 2.80/1.02      ( ~ r2_funct_2(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,k2_tmap_1(X2_47,X1_47,X1_48,X0_47))
% 2.80/1.02      | r2_funct_2(u1_struct_0(X3_47),u1_struct_0(X1_47),k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),k2_tmap_1(X2_47,X1_47,X1_48,X3_47))
% 2.80/1.02      | ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
% 2.80/1.02      | ~ v1_funct_2(X1_48,u1_struct_0(X2_47),u1_struct_0(X1_47))
% 2.80/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
% 2.80/1.02      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_47),u1_struct_0(X1_47))))
% 2.80/1.02      | ~ m1_pre_topc(X3_47,X2_47)
% 2.80/1.02      | ~ m1_pre_topc(X3_47,X0_47)
% 2.80/1.02      | ~ m1_pre_topc(X0_47,X2_47)
% 2.80/1.02      | v2_struct_0(X3_47)
% 2.80/1.02      | v2_struct_0(X1_47)
% 2.80/1.02      | v2_struct_0(X0_47)
% 2.80/1.02      | v2_struct_0(X2_47)
% 2.80/1.02      | ~ v2_pre_topc(X1_47)
% 2.80/1.02      | ~ v2_pre_topc(X2_47)
% 2.80/1.02      | ~ l1_pre_topc(X1_47)
% 2.80/1.02      | ~ l1_pre_topc(X2_47)
% 2.80/1.02      | ~ v1_funct_1(X1_48)
% 2.80/1.02      | ~ v1_funct_1(X0_48) ),
% 2.80/1.02      inference(subtyping,[status(esa)],[c_7]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_678,plain,
% 2.80/1.02      ( r2_funct_2(u1_struct_0(X0_47),u1_struct_0(X1_47),X0_48,k2_tmap_1(X2_47,X1_47,X1_48,X0_47)) != iProver_top
% 2.80/1.02      | r2_funct_2(u1_struct_0(X3_47),u1_struct_0(X1_47),k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),k2_tmap_1(X2_47,X1_47,X1_48,X3_47)) = iProver_top
% 2.80/1.02      | v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
% 2.80/1.02      | v1_funct_2(X1_48,u1_struct_0(X2_47),u1_struct_0(X1_47)) != iProver_top
% 2.80/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
% 2.80/1.02      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_47),u1_struct_0(X1_47)))) != iProver_top
% 2.80/1.02      | m1_pre_topc(X3_47,X0_47) != iProver_top
% 2.80/1.02      | m1_pre_topc(X0_47,X2_47) != iProver_top
% 2.80/1.02      | m1_pre_topc(X3_47,X2_47) != iProver_top
% 2.80/1.02      | v2_struct_0(X3_47) = iProver_top
% 2.80/1.02      | v2_struct_0(X1_47) = iProver_top
% 2.80/1.02      | v2_struct_0(X0_47) = iProver_top
% 2.80/1.02      | v2_struct_0(X2_47) = iProver_top
% 2.80/1.02      | v2_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | v2_pre_topc(X2_47) != iProver_top
% 2.80/1.02      | l1_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | l1_pre_topc(X2_47) != iProver_top
% 2.80/1.02      | v1_funct_1(X0_48) != iProver_top
% 2.80/1.02      | v1_funct_1(X1_48) != iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_256]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_3875,plain,
% 2.80/1.02      ( r2_funct_2(u1_struct_0(X0_47),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_47,sK4),k2_tmap_1(sK0,sK1,sK4,X0_47)) = iProver_top
% 2.80/1.02      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.80/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.80/1.02      | m1_pre_topc(X0_47,sK0) != iProver_top
% 2.80/1.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.80/1.02      | v2_struct_0(X0_47) = iProver_top
% 2.80/1.02      | v2_struct_0(sK0) = iProver_top
% 2.80/1.02      | v2_struct_0(sK1) = iProver_top
% 2.80/1.02      | v2_pre_topc(sK0) != iProver_top
% 2.80/1.02      | v2_pre_topc(sK1) != iProver_top
% 2.80/1.02      | l1_pre_topc(sK0) != iProver_top
% 2.80/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.80/1.02      | v1_funct_1(sK4) != iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_3870,c_678]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_10677,plain,
% 2.80/1.02      ( v2_struct_0(X0_47) = iProver_top
% 2.80/1.02      | r2_funct_2(u1_struct_0(X0_47),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_47,sK4),k2_tmap_1(sK0,sK1,sK4,X0_47)) = iProver_top
% 2.80/1.02      | m1_pre_topc(X0_47,sK0) != iProver_top ),
% 2.80/1.02      inference(global_propositional_subsumption,
% 2.80/1.02                [status(thm)],
% 2.80/1.02                [c_3875,c_23,c_24,c_25,c_26,c_27,c_28,c_33,c_34,c_35,
% 2.80/1.02                 c_46]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_10678,plain,
% 2.80/1.02      ( r2_funct_2(u1_struct_0(X0_47),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,X0_47,sK4),k2_tmap_1(sK0,sK1,sK4,X0_47)) = iProver_top
% 2.80/1.02      | m1_pre_topc(X0_47,sK0) != iProver_top
% 2.80/1.02      | v2_struct_0(X0_47) = iProver_top ),
% 2.80/1.02      inference(renaming,[status(thm)],[c_10677]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_10687,plain,
% 2.80/1.02      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top
% 2.80/1.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.80/1.02      | v2_struct_0(sK3) = iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_2367,c_10678]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_1107,plain,
% 2.80/1.02      ( ~ r2_funct_2(u1_struct_0(X0_47),u1_struct_0(sK1),X0_48,k2_tmap_1(X1_47,sK1,X1_48,X0_47))
% 2.80/1.02      | r2_funct_2(u1_struct_0(X2_47),u1_struct_0(sK1),k3_tmap_1(X1_47,sK1,X0_47,X2_47,X0_48),k2_tmap_1(X1_47,sK1,X1_48,X2_47))
% 2.80/1.02      | ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(sK1))
% 2.80/1.02      | ~ v1_funct_2(X1_48,u1_struct_0(X1_47),u1_struct_0(sK1))
% 2.80/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(sK1))))
% 2.80/1.02      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_47),u1_struct_0(sK1))))
% 2.80/1.02      | ~ m1_pre_topc(X2_47,X0_47)
% 2.80/1.02      | ~ m1_pre_topc(X0_47,X1_47)
% 2.80/1.02      | ~ m1_pre_topc(X2_47,X1_47)
% 2.80/1.02      | v2_struct_0(X1_47)
% 2.80/1.02      | v2_struct_0(X0_47)
% 2.80/1.02      | v2_struct_0(X2_47)
% 2.80/1.02      | v2_struct_0(sK1)
% 2.80/1.02      | ~ v2_pre_topc(X1_47)
% 2.80/1.02      | ~ v2_pre_topc(sK1)
% 2.80/1.02      | ~ l1_pre_topc(X1_47)
% 2.80/1.02      | ~ l1_pre_topc(sK1)
% 2.80/1.02      | ~ v1_funct_1(X1_48)
% 2.80/1.02      | ~ v1_funct_1(X0_48) ),
% 2.80/1.02      inference(instantiation,[status(thm)],[c_256]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_6444,plain,
% 2.80/1.02      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3))
% 2.80/1.02      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
% 2.80/1.02      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 2.80/1.02      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.80/1.02      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.80/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.80/1.02      | ~ m1_pre_topc(sK3,sK0)
% 2.80/1.02      | ~ m1_pre_topc(sK2,sK3)
% 2.80/1.02      | ~ m1_pre_topc(sK2,sK0)
% 2.80/1.02      | v2_struct_0(sK3)
% 2.80/1.02      | v2_struct_0(sK0)
% 2.80/1.02      | v2_struct_0(sK1)
% 2.80/1.02      | v2_struct_0(sK2)
% 2.80/1.02      | ~ v2_pre_topc(sK0)
% 2.80/1.02      | ~ v2_pre_topc(sK1)
% 2.80/1.02      | ~ l1_pre_topc(sK0)
% 2.80/1.02      | ~ l1_pre_topc(sK1)
% 2.80/1.02      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
% 2.80/1.02      | ~ v1_funct_1(sK4) ),
% 2.80/1.02      inference(instantiation,[status(thm)],[c_1107]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_6445,plain,
% 2.80/1.02      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 2.80/1.02      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
% 2.80/1.02      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.80/1.02      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.80/1.02      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.80/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.80/1.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.80/1.02      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.80/1.02      | m1_pre_topc(sK2,sK0) != iProver_top
% 2.80/1.02      | v2_struct_0(sK3) = iProver_top
% 2.80/1.02      | v2_struct_0(sK0) = iProver_top
% 2.80/1.02      | v2_struct_0(sK1) = iProver_top
% 2.80/1.02      | v2_struct_0(sK2) = iProver_top
% 2.80/1.02      | v2_pre_topc(sK0) != iProver_top
% 2.80/1.02      | v2_pre_topc(sK1) != iProver_top
% 2.80/1.02      | l1_pre_topc(sK0) != iProver_top
% 2.80/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.80/1.02      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 2.80/1.02      | v1_funct_1(sK4) != iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_6444]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_4,plain,
% 2.80/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.80/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.80/1.02      | ~ m1_pre_topc(X3,X4)
% 2.80/1.02      | ~ m1_pre_topc(X1,X4)
% 2.80/1.02      | v2_struct_0(X4)
% 2.80/1.02      | v2_struct_0(X2)
% 2.80/1.02      | ~ v2_pre_topc(X2)
% 2.80/1.02      | ~ v2_pre_topc(X4)
% 2.80/1.02      | ~ l1_pre_topc(X2)
% 2.80/1.02      | ~ l1_pre_topc(X4)
% 2.80/1.02      | ~ v1_funct_1(X0)
% 2.80/1.02      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 2.80/1.02      inference(cnf_transformation,[],[f30]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_259,plain,
% 2.80/1.02      ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
% 2.80/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
% 2.80/1.02      | ~ m1_pre_topc(X0_47,X2_47)
% 2.80/1.02      | ~ m1_pre_topc(X3_47,X2_47)
% 2.80/1.02      | v2_struct_0(X2_47)
% 2.80/1.02      | v2_struct_0(X1_47)
% 2.80/1.02      | ~ v2_pre_topc(X1_47)
% 2.80/1.02      | ~ v2_pre_topc(X2_47)
% 2.80/1.02      | ~ l1_pre_topc(X1_47)
% 2.80/1.02      | ~ l1_pre_topc(X2_47)
% 2.80/1.02      | ~ v1_funct_1(X0_48)
% 2.80/1.02      | v1_funct_1(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48)) ),
% 2.80/1.02      inference(subtyping,[status(esa)],[c_4]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_675,plain,
% 2.80/1.02      ( v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
% 2.80/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
% 2.80/1.02      | m1_pre_topc(X0_47,X2_47) != iProver_top
% 2.80/1.02      | m1_pre_topc(X3_47,X2_47) != iProver_top
% 2.80/1.02      | v2_struct_0(X1_47) = iProver_top
% 2.80/1.02      | v2_struct_0(X2_47) = iProver_top
% 2.80/1.02      | v2_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | v2_pre_topc(X2_47) != iProver_top
% 2.80/1.02      | l1_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | l1_pre_topc(X2_47) != iProver_top
% 2.80/1.02      | v1_funct_1(X0_48) != iProver_top
% 2.80/1.02      | v1_funct_1(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48)) = iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_259]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_1676,plain,
% 2.80/1.02      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.80/1.02      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.80/1.02      | m1_pre_topc(sK0,X1_47) != iProver_top
% 2.80/1.02      | v2_struct_0(X1_47) = iProver_top
% 2.80/1.02      | v2_struct_0(sK1) = iProver_top
% 2.80/1.02      | v2_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | v2_pre_topc(sK1) != iProver_top
% 2.80/1.02      | l1_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.80/1.02      | v1_funct_1(k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)) = iProver_top
% 2.80/1.02      | v1_funct_1(sK4) != iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_681,c_675]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2020,plain,
% 2.80/1.02      ( v1_funct_1(k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)) = iProver_top
% 2.80/1.02      | v2_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.80/1.02      | m1_pre_topc(sK0,X1_47) != iProver_top
% 2.80/1.02      | v2_struct_0(X1_47) = iProver_top
% 2.80/1.02      | l1_pre_topc(X1_47) != iProver_top ),
% 2.80/1.02      inference(global_propositional_subsumption,
% 2.80/1.02                [status(thm)],
% 2.80/1.02                [c_1676,c_26,c_27,c_28,c_33,c_34]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2021,plain,
% 2.80/1.02      ( m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.80/1.02      | m1_pre_topc(sK0,X1_47) != iProver_top
% 2.80/1.02      | v2_struct_0(X1_47) = iProver_top
% 2.80/1.02      | v2_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | l1_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | v1_funct_1(k3_tmap_1(X1_47,sK1,sK0,X0_47,sK4)) = iProver_top ),
% 2.80/1.02      inference(renaming,[status(thm)],[c_2020]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2372,plain,
% 2.80/1.02      ( m1_pre_topc(sK3,sK0) != iProver_top
% 2.80/1.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.80/1.02      | v2_struct_0(sK0) = iProver_top
% 2.80/1.02      | v2_pre_topc(sK0) != iProver_top
% 2.80/1.02      | l1_pre_topc(sK0) != iProver_top
% 2.80/1.02      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
% 2.80/1.02      inference(superposition,[status(thm)],[c_2367,c_2021]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_3,plain,
% 2.80/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.80/1.02      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 2.80/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.80/1.02      | ~ m1_pre_topc(X4,X3)
% 2.80/1.02      | ~ m1_pre_topc(X1,X3)
% 2.80/1.02      | v2_struct_0(X3)
% 2.80/1.02      | v2_struct_0(X2)
% 2.80/1.02      | ~ v2_pre_topc(X2)
% 2.80/1.02      | ~ v2_pre_topc(X3)
% 2.80/1.02      | ~ l1_pre_topc(X2)
% 2.80/1.02      | ~ l1_pre_topc(X3)
% 2.80/1.02      | ~ v1_funct_1(X0) ),
% 2.80/1.02      inference(cnf_transformation,[],[f31]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_260,plain,
% 2.80/1.02      ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
% 2.80/1.02      | v1_funct_2(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),u1_struct_0(X3_47),u1_struct_0(X1_47))
% 2.80/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
% 2.80/1.02      | ~ m1_pre_topc(X3_47,X2_47)
% 2.80/1.02      | ~ m1_pre_topc(X0_47,X2_47)
% 2.80/1.02      | v2_struct_0(X1_47)
% 2.80/1.02      | v2_struct_0(X2_47)
% 2.80/1.02      | ~ v2_pre_topc(X1_47)
% 2.80/1.02      | ~ v2_pre_topc(X2_47)
% 2.80/1.02      | ~ l1_pre_topc(X1_47)
% 2.80/1.02      | ~ l1_pre_topc(X2_47)
% 2.80/1.02      | ~ v1_funct_1(X0_48) ),
% 2.80/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_674,plain,
% 2.80/1.02      ( v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
% 2.80/1.02      | v1_funct_2(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),u1_struct_0(X3_47),u1_struct_0(X1_47)) = iProver_top
% 2.80/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
% 2.80/1.02      | m1_pre_topc(X0_47,X2_47) != iProver_top
% 2.80/1.02      | m1_pre_topc(X3_47,X2_47) != iProver_top
% 2.80/1.02      | v2_struct_0(X1_47) = iProver_top
% 2.80/1.02      | v2_struct_0(X2_47) = iProver_top
% 2.80/1.02      | v2_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | v2_pre_topc(X2_47) != iProver_top
% 2.80/1.02      | l1_pre_topc(X1_47) != iProver_top
% 2.80/1.02      | l1_pre_topc(X2_47) != iProver_top
% 2.80/1.02      | v1_funct_1(X0_48) != iProver_top ),
% 2.80/1.02      inference(predicate_to_equality,[status(thm)],[c_260]) ).
% 2.80/1.02  
% 2.80/1.02  cnf(c_2371,plain,
% 2.80/1.02      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 2.80/1.02      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.80/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.80/1.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.80/1.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.80/1.02      | v2_struct_0(sK0) = iProver_top
% 2.80/1.02      | v2_struct_0(sK1) = iProver_top
% 2.80/1.02      | v2_pre_topc(sK0) != iProver_top
% 2.80/1.02      | v2_pre_topc(sK1) != iProver_top
% 2.80/1.02      | l1_pre_topc(sK0) != iProver_top
% 2.80/1.03      | l1_pre_topc(sK1) != iProver_top
% 2.80/1.03      | v1_funct_1(sK4) != iProver_top ),
% 2.80/1.03      inference(superposition,[status(thm)],[c_2367,c_674]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_2,plain,
% 2.80/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.80/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.80/1.03      | m1_subset_1(k3_tmap_1(X3,X2,X1,X4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 2.80/1.03      | ~ m1_pre_topc(X4,X3)
% 2.80/1.03      | ~ m1_pre_topc(X1,X3)
% 2.80/1.03      | v2_struct_0(X3)
% 2.80/1.03      | v2_struct_0(X2)
% 2.80/1.03      | ~ v2_pre_topc(X2)
% 2.80/1.03      | ~ v2_pre_topc(X3)
% 2.80/1.03      | ~ l1_pre_topc(X2)
% 2.80/1.03      | ~ l1_pre_topc(X3)
% 2.80/1.03      | ~ v1_funct_1(X0) ),
% 2.80/1.03      inference(cnf_transformation,[],[f32]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_261,plain,
% 2.80/1.03      ( ~ v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47))
% 2.80/1.03      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
% 2.80/1.03      | m1_subset_1(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_47),u1_struct_0(X1_47))))
% 2.80/1.03      | ~ m1_pre_topc(X3_47,X2_47)
% 2.80/1.03      | ~ m1_pre_topc(X0_47,X2_47)
% 2.80/1.03      | v2_struct_0(X1_47)
% 2.80/1.03      | v2_struct_0(X2_47)
% 2.80/1.03      | ~ v2_pre_topc(X1_47)
% 2.80/1.03      | ~ v2_pre_topc(X2_47)
% 2.80/1.03      | ~ l1_pre_topc(X1_47)
% 2.80/1.03      | ~ l1_pre_topc(X2_47)
% 2.80/1.03      | ~ v1_funct_1(X0_48) ),
% 2.80/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_673,plain,
% 2.80/1.03      ( v1_funct_2(X0_48,u1_struct_0(X0_47),u1_struct_0(X1_47)) != iProver_top
% 2.80/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) != iProver_top
% 2.80/1.03      | m1_subset_1(k3_tmap_1(X2_47,X1_47,X0_47,X3_47,X0_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_47),u1_struct_0(X1_47)))) = iProver_top
% 2.80/1.03      | m1_pre_topc(X0_47,X2_47) != iProver_top
% 2.80/1.03      | m1_pre_topc(X3_47,X2_47) != iProver_top
% 2.80/1.03      | v2_struct_0(X1_47) = iProver_top
% 2.80/1.03      | v2_struct_0(X2_47) = iProver_top
% 2.80/1.03      | v2_pre_topc(X1_47) != iProver_top
% 2.80/1.03      | v2_pre_topc(X2_47) != iProver_top
% 2.80/1.03      | l1_pre_topc(X1_47) != iProver_top
% 2.80/1.03      | l1_pre_topc(X2_47) != iProver_top
% 2.80/1.03      | v1_funct_1(X0_48) != iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_261]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_2370,plain,
% 2.80/1.03      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.80/1.03      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 2.80/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.80/1.03      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.80/1.03      | m1_pre_topc(sK0,sK0) != iProver_top
% 2.80/1.03      | v2_struct_0(sK0) = iProver_top
% 2.80/1.03      | v2_struct_0(sK1) = iProver_top
% 2.80/1.03      | v2_pre_topc(sK0) != iProver_top
% 2.80/1.03      | v2_pre_topc(sK1) != iProver_top
% 2.80/1.03      | l1_pre_topc(sK0) != iProver_top
% 2.80/1.03      | l1_pre_topc(sK1) != iProver_top
% 2.80/1.03      | v1_funct_1(sK4) != iProver_top ),
% 2.80/1.03      inference(superposition,[status(thm)],[c_2367,c_673]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_8,negated_conjecture,
% 2.80/1.03      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) ),
% 2.80/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_37,plain,
% 2.80/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_9,negated_conjecture,
% 2.80/1.03      ( m1_pre_topc(sK2,sK3) ),
% 2.80/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_36,plain,
% 2.80/1.03      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_14,negated_conjecture,
% 2.80/1.03      ( ~ v2_struct_0(sK3) ),
% 2.80/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_31,plain,
% 2.80/1.03      ( v2_struct_0(sK3) != iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_15,negated_conjecture,
% 2.80/1.03      ( m1_pre_topc(sK2,sK0) ),
% 2.80/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_30,plain,
% 2.80/1.03      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_16,negated_conjecture,
% 2.80/1.03      ( ~ v2_struct_0(sK2) ),
% 2.80/1.03      inference(cnf_transformation,[],[f42]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(c_29,plain,
% 2.80/1.03      ( v2_struct_0(sK2) != iProver_top ),
% 2.80/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.80/1.03  
% 2.80/1.03  cnf(contradiction,plain,
% 2.80/1.03      ( $false ),
% 2.80/1.03      inference(minisat,
% 2.80/1.03                [status(thm)],
% 2.80/1.03                [c_10687,c_6445,c_2372,c_2371,c_2370,c_46,c_37,c_36,c_35,
% 2.80/1.03                 c_34,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25,c_24,
% 2.80/1.03                 c_23]) ).
% 2.80/1.03  
% 2.80/1.03  
% 2.80/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.80/1.03  
% 2.80/1.03  ------                               Statistics
% 2.80/1.03  
% 2.80/1.03  ------ General
% 2.80/1.03  
% 2.80/1.03  abstr_ref_over_cycles:                  0
% 2.80/1.03  abstr_ref_under_cycles:                 0
% 2.80/1.03  gc_basic_clause_elim:                   0
% 2.80/1.03  forced_gc_time:                         0
% 2.80/1.03  parsing_time:                           0.014
% 2.80/1.03  unif_index_cands_time:                  0.
% 2.80/1.03  unif_index_add_time:                    0.
% 2.80/1.03  orderings_time:                         0.
% 2.80/1.03  out_proof_time:                         0.013
% 2.80/1.03  total_time:                             0.396
% 2.80/1.03  num_of_symbols:                         52
% 2.80/1.03  num_of_terms:                           6325
% 2.80/1.03  
% 2.80/1.03  ------ Preprocessing
% 2.80/1.03  
% 2.80/1.03  num_of_splits:                          0
% 2.80/1.03  num_of_split_atoms:                     0
% 2.80/1.03  num_of_reused_defs:                     0
% 2.80/1.03  num_eq_ax_congr_red:                    26
% 2.80/1.03  num_of_sem_filtered_clauses:            1
% 2.80/1.03  num_of_subtypes:                        5
% 2.80/1.03  monotx_restored_types:                  0
% 2.80/1.03  sat_num_of_epr_types:                   0
% 2.80/1.03  sat_num_of_non_cyclic_types:            0
% 2.80/1.03  sat_guarded_non_collapsed_types:        0
% 2.80/1.03  num_pure_diseq_elim:                    0
% 2.80/1.03  simp_replaced_by:                       0
% 2.80/1.03  res_preprocessed:                       86
% 2.80/1.03  prep_upred:                             0
% 2.80/1.03  prep_unflattend:                        0
% 2.80/1.03  smt_new_axioms:                         0
% 2.80/1.03  pred_elim_cands:                        8
% 2.80/1.03  pred_elim:                              0
% 2.80/1.03  pred_elim_cl:                           0
% 2.80/1.03  pred_elim_cycles:                       1
% 2.80/1.03  merged_defs:                            0
% 2.80/1.03  merged_defs_ncl:                        0
% 2.80/1.03  bin_hyper_res:                          0
% 2.80/1.03  prep_cycles:                            3
% 2.80/1.03  pred_elim_time:                         0.
% 2.80/1.03  splitting_time:                         0.
% 2.80/1.03  sem_filter_time:                        0.
% 2.80/1.03  monotx_time:                            0.
% 2.80/1.03  subtype_inf_time:                       0.
% 2.80/1.03  
% 2.80/1.03  ------ Problem properties
% 2.80/1.03  
% 2.80/1.03  clauses:                                23
% 2.80/1.03  conjectures:                            15
% 2.80/1.03  epr:                                    13
% 2.80/1.03  horn:                                   16
% 2.80/1.03  ground:                                 15
% 2.80/1.03  unary:                                  15
% 2.80/1.03  binary:                                 1
% 2.80/1.03  lits:                                   108
% 2.80/1.03  lits_eq:                                2
% 2.80/1.03  fd_pure:                                0
% 2.80/1.03  fd_pseudo:                              0
% 2.80/1.03  fd_cond:                                0
% 2.80/1.03  fd_pseudo_cond:                         0
% 2.80/1.03  ac_symbols:                             0
% 2.80/1.03  
% 2.80/1.03  ------ Propositional Solver
% 2.80/1.03  
% 2.80/1.03  prop_solver_calls:                      25
% 2.80/1.03  prop_fast_solver_calls:                 1746
% 2.80/1.03  smt_solver_calls:                       0
% 2.80/1.03  smt_fast_solver_calls:                  0
% 2.80/1.03  prop_num_of_clauses:                    2203
% 2.80/1.03  prop_preprocess_simplified:             6632
% 2.80/1.03  prop_fo_subsumed:                       265
% 2.80/1.03  prop_solver_time:                       0.
% 2.80/1.03  smt_solver_time:                        0.
% 2.80/1.03  smt_fast_solver_time:                   0.
% 2.80/1.03  prop_fast_solver_time:                  0.
% 2.80/1.03  prop_unsat_core_time:                   0.
% 2.80/1.03  
% 2.80/1.03  ------ QBF
% 2.80/1.03  
% 2.80/1.03  qbf_q_res:                              0
% 2.80/1.03  qbf_num_tautologies:                    0
% 2.80/1.03  qbf_prep_cycles:                        0
% 2.80/1.03  
% 2.80/1.03  ------ BMC1
% 2.80/1.03  
% 2.80/1.03  bmc1_current_bound:                     -1
% 2.80/1.03  bmc1_last_solved_bound:                 -1
% 2.80/1.03  bmc1_unsat_core_size:                   -1
% 2.80/1.03  bmc1_unsat_core_parents_size:           -1
% 2.80/1.03  bmc1_merge_next_fun:                    0
% 2.80/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.80/1.03  
% 2.80/1.03  ------ Instantiation
% 2.80/1.03  
% 2.80/1.03  inst_num_of_clauses:                    877
% 2.80/1.03  inst_num_in_passive:                    141
% 2.80/1.03  inst_num_in_active:                     433
% 2.80/1.03  inst_num_in_unprocessed:                303
% 2.80/1.03  inst_num_of_loops:                      490
% 2.80/1.03  inst_num_of_learning_restarts:          0
% 2.80/1.03  inst_num_moves_active_passive:          51
% 2.80/1.03  inst_lit_activity:                      0
% 2.80/1.03  inst_lit_activity_moves:                0
% 2.80/1.03  inst_num_tautologies:                   0
% 2.80/1.03  inst_num_prop_implied:                  0
% 2.80/1.03  inst_num_existing_simplified:           0
% 2.80/1.03  inst_num_eq_res_simplified:             0
% 2.80/1.03  inst_num_child_elim:                    0
% 2.80/1.03  inst_num_of_dismatching_blockings:      1042
% 2.80/1.03  inst_num_of_non_proper_insts:           1479
% 2.80/1.03  inst_num_of_duplicates:                 0
% 2.80/1.03  inst_inst_num_from_inst_to_res:         0
% 2.80/1.03  inst_dismatching_checking_time:         0.
% 2.80/1.03  
% 2.80/1.03  ------ Resolution
% 2.80/1.03  
% 2.80/1.03  res_num_of_clauses:                     0
% 2.80/1.03  res_num_in_passive:                     0
% 2.80/1.03  res_num_in_active:                      0
% 2.80/1.03  res_num_of_loops:                       89
% 2.80/1.03  res_forward_subset_subsumed:            238
% 2.80/1.03  res_backward_subset_subsumed:           0
% 2.80/1.03  res_forward_subsumed:                   0
% 2.80/1.03  res_backward_subsumed:                  0
% 2.80/1.03  res_forward_subsumption_resolution:     0
% 2.80/1.03  res_backward_subsumption_resolution:    0
% 2.80/1.03  res_clause_to_clause_subsumption:       671
% 2.80/1.03  res_orphan_elimination:                 0
% 2.80/1.03  res_tautology_del:                      310
% 2.80/1.03  res_num_eq_res_simplified:              0
% 2.80/1.03  res_num_sel_changes:                    0
% 2.80/1.03  res_moves_from_active_to_pass:          0
% 2.80/1.03  
% 2.80/1.03  ------ Superposition
% 2.80/1.03  
% 2.80/1.03  sup_time_total:                         0.
% 2.80/1.03  sup_time_generating:                    0.
% 2.80/1.03  sup_time_sim_full:                      0.
% 2.80/1.03  sup_time_sim_immed:                     0.
% 2.80/1.03  
% 2.80/1.03  sup_num_of_clauses:                     121
% 2.80/1.03  sup_num_in_active:                      97
% 2.80/1.03  sup_num_in_passive:                     24
% 2.80/1.03  sup_num_of_loops:                       97
% 2.80/1.03  sup_fw_superposition:                   75
% 2.80/1.03  sup_bw_superposition:                   34
% 2.80/1.03  sup_immediate_simplified:               21
% 2.80/1.03  sup_given_eliminated:                   0
% 2.80/1.03  comparisons_done:                       0
% 2.80/1.03  comparisons_avoided:                    0
% 2.80/1.03  
% 2.80/1.03  ------ Simplifications
% 2.80/1.03  
% 2.80/1.03  
% 2.80/1.03  sim_fw_subset_subsumed:                 1
% 2.80/1.03  sim_bw_subset_subsumed:                 0
% 2.80/1.03  sim_fw_subsumed:                        6
% 2.80/1.03  sim_bw_subsumed:                        0
% 2.80/1.03  sim_fw_subsumption_res:                 6
% 2.80/1.03  sim_bw_subsumption_res:                 0
% 2.80/1.03  sim_tautology_del:                      0
% 2.80/1.03  sim_eq_tautology_del:                   0
% 2.80/1.03  sim_eq_res_simp:                        0
% 2.80/1.03  sim_fw_demodulated:                     0
% 2.80/1.03  sim_bw_demodulated:                     1
% 2.80/1.03  sim_light_normalised:                   20
% 2.80/1.03  sim_joinable_taut:                      0
% 2.80/1.03  sim_joinable_simp:                      0
% 2.80/1.03  sim_ac_normalised:                      0
% 2.80/1.03  sim_smt_subsumption:                    0
% 2.80/1.03  
%------------------------------------------------------------------------------
