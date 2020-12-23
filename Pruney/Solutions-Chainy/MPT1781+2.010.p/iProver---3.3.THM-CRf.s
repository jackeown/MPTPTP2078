%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:45 EST 2020

% Result     : Theorem 7.23s
% Output     : CNFRefutation 7.23s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2919)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,u1_struct_0(X1))
                     => k1_funct_1(X2,X3) = X3 ) )
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,u1_struct_0(X1))
                       => k1_funct_1(X2,X3) = X3 ) )
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
          & ! [X3] :
              ( k1_funct_1(X2,X3) = X3
              | ~ r2_hidden(X3,u1_struct_0(X1))
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
     => ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK3)
        & ! [X3] :
            ( k1_funct_1(sK3,X3) = X3
            | ~ r2_hidden(X3,u1_struct_0(X1))
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k4_tmap_1(X0,sK2),X2)
            & ! [X3] :
                ( k1_funct_1(X2,X3) = X3
                | ~ r2_hidden(X3,u1_struct_0(sK2))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
                & ! [X3] :
                    ( k1_funct_1(X2,X3) = X3
                    | ~ r2_hidden(X3,u1_struct_0(X1))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK1),k4_tmap_1(sK1,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
    & ! [X3] :
        ( k1_funct_1(sK3,X3) = X3
        | ~ r2_hidden(X3,u1_struct_0(sK2))
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f52,f58,f57,f56])).

fof(f88,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f91,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f85,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f86,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f90,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f59])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

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
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f54,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
        & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
                        & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
                        & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f54])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,u1_struct_0(X1))
               => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f93,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f63])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2049,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | m1_subset_1(k4_tmap_1(X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2622,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_subset_1(k4_tmap_1(X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2049])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2034,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_2637,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2034])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2037,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_2634,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2037])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2053,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X2_52,X0_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | ~ m1_pre_topc(X2_52,X3_52)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | v2_struct_0(X1_52)
    | v2_struct_0(X3_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X3_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X3_52)
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_54,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_54) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2618,plain,
    ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_54,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_54)
    | v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_pre_topc(X0_52,X3_52) != iProver_top
    | m1_pre_topc(X2_52,X3_52) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X3_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X3_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X3_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2053])).

cnf(c_5174,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK2,X0_52,sK3)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_2618])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_34,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_35,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_36,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_40,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5918,plain,
    ( l1_pre_topc(X1_52) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK2,X0_52,sK3)
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5174,c_34,c_35,c_36,c_39,c_40,c_41,c_2919])).

cnf(c_5919,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK2,X0_52,sK3)
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_5918])).

cnf(c_5924,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k3_tmap_1(sK1,sK1,sK2,sK2,sK3)
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2637,c_5919])).

cnf(c_17,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2046,plain,
    ( m1_pre_topc(X0_52,X0_52)
    | ~ l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2625,plain,
    ( m1_pre_topc(X0_52,X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2046])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2054,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X2_52,X0_52)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X0_52)
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_54,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_54,X2_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2617,plain,
    ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_54,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_54,X2_52)
    | v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2054])).

cnf(c_4494,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_52)) = k2_tmap_1(sK2,sK1,sK3,X0_52)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_52,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_2617])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_37,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_38,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2056,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ l1_pre_topc(X1_52)
    | l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2873,plain,
    ( ~ m1_pre_topc(sK2,X0_52)
    | ~ l1_pre_topc(X0_52)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2056])).

cnf(c_2874,plain,
    ( m1_pre_topc(sK2,X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2873])).

cnf(c_2876,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2874])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2057,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52)
    | v2_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3148,plain,
    ( ~ m1_pre_topc(sK2,X0_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X0_52)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2057])).

cnf(c_3149,plain,
    ( m1_pre_topc(sK2,X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3148])).

cnf(c_3151,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3149])).

cnf(c_4964,plain,
    ( m1_pre_topc(X0_52,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_52)) = k2_tmap_1(sK2,sK1,sK3,X0_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4494,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_2876,c_3151])).

cnf(c_4965,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_52)) = k2_tmap_1(sK2,sK1,sK3,X0_52)
    | m1_pre_topc(X0_52,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4964])).

cnf(c_4970,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2625,c_4965])).

cnf(c_2875,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2873])).

cnf(c_3150,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3148])).

cnf(c_3685,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2046])).

cnf(c_2737,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_52))
    | ~ m1_pre_topc(X1_52,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52))))
    | v2_struct_0(X0_52)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0_52),X0_54,u1_struct_0(X1_52)) = k2_tmap_1(sK2,X0_52,X0_54,X1_52) ),
    inference(instantiation,[status(thm)],[c_2054])).

cnf(c_3693,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_52))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52))))
    | v2_struct_0(X0_52)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0_52),X0_54,u1_struct_0(sK2)) = k2_tmap_1(sK2,X0_52,X0_54,sK2) ),
    inference(instantiation,[status(thm)],[c_2737])).

cnf(c_3695,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_3693])).

cnf(c_5011,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4970,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_2875,c_3150,c_3685,c_3695])).

cnf(c_5926,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2)
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5924,c_5011])).

cnf(c_3686,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3685])).

cnf(c_6150,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5926,c_34,c_35,c_36,c_38,c_2876,c_3686])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2052,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_pre_topc(X3_52,X2_52)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | m1_subset_1(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2619,plain,
    ( v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_pre_topc(X3_52,X2_52) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52)))) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2052])).

cnf(c_6153,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6150,c_2619])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7144,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6153,c_34,c_35,c_36,c_38,c_39,c_40,c_41])).

cnf(c_3,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2058,plain,
    ( ~ r2_funct_2(X0_53,X1_53,X0_54,X1_54)
    | ~ v1_funct_2(X0_54,X0_53,X1_53)
    | ~ v1_funct_2(X1_54,X0_53,X1_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | X1_54 = X0_54 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2613,plain,
    ( X0_54 = X1_54
    | r2_funct_2(X0_53,X1_53,X1_54,X0_54) != iProver_top
    | v1_funct_2(X1_54,X0_53,X1_53) != iProver_top
    | v1_funct_2(X0_54,X0_53,X1_53) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2058])).

cnf(c_3920,plain,
    ( sK3 = X0_54
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,sK3) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_2613])).

cnf(c_3927,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | sK3 = X0_54
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,sK3) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3920,c_39,c_40])).

cnf(c_3928,plain,
    ( sK3 = X0_54
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,sK3) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3927])).

cnf(c_7155,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7144,c_3928])).

cnf(c_21,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2042,plain,
    ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_54,k3_tmap_1(X2_52,X1_52,X0_52,X0_52,X0_54))
    | ~ v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2629,plain,
    ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_54,k3_tmap_1(X2_52,X1_52,X0_52,X0_52,X0_54)) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2042])).

cnf(c_6152,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6150,c_2629])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2051,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | v1_funct_2(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_54),u1_struct_0(X3_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_pre_topc(X3_52,X2_52)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2620,plain,
    ( v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_54),u1_struct_0(X3_52),u1_struct_0(X1_52)) = iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_pre_topc(X3_52,X2_52) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2051])).

cnf(c_6154,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6150,c_2620])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2050,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_pre_topc(X3_52,X2_52)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_54)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2621,plain,
    ( v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_pre_topc(X3_52,X2_52) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2050])).

cnf(c_4503,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(sK2,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_52,sK1,sK2,X0_52,sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_2621])).

cnf(c_2713,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_pre_topc(X2_52,X1_52)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1))))
    | v2_struct_0(X1_52)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k3_tmap_1(X1_52,sK1,X0_52,X2_52,X0_54)) ),
    inference(instantiation,[status(thm)],[c_2050])).

cnf(c_2819,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_pre_topc(sK2,X1_52)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(X1_52)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(X1_52,sK1,sK2,X0_52,sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2713])).

cnf(c_2820,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(sK2,X1_52) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_52,sK1,sK2,X0_52,sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2819])).

cnf(c_5004,plain,
    ( v1_funct_1(k3_tmap_1(X1_52,sK1,sK2,X0_52,sK3)) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(sK2,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4503,c_34,c_35,c_36,c_39,c_40])).

cnf(c_5005,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(sK2,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_52,sK1,sK2,X0_52,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5004])).

cnf(c_6155,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6150,c_5005])).

cnf(c_7151,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = X0_54
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7144,c_2613])).

cnf(c_7166,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7151])).

cnf(c_7175,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7155,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_6152,c_6154,c_6155,c_7166])).

cnf(c_19,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2044,plain,
    ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_54,X0_52),X1_54)
    | ~ v1_funct_2(X1_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ v1_funct_2(X0_54,u1_struct_0(X2_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | r2_hidden(sK0(X1_52,X2_52,X0_52,X0_54,X1_54),u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2627,plain,
    ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_54,X0_52),X1_54) = iProver_top
    | v1_funct_2(X1_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
    | r2_hidden(sK0(X1_52,X2_52,X0_52,X0_54,X1_54),u1_struct_0(X0_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2044])).

cnf(c_7184,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7175,c_2627])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_370,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_5,c_7])).

cnf(c_2029,plain,
    ( v2_struct_0(X0_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v1_xboole_0(u1_struct_0(X0_52)) ),
    inference(subtyping,[status(esa)],[c_370])).

cnf(c_2741,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2029])).

cnf(c_2742,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2741])).

cnf(c_20,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,X2,X0,X3,X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2043,plain,
    ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_54,X0_52),X1_54)
    | ~ v1_funct_2(X1_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ v1_funct_2(X0_54,u1_struct_0(X2_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | m1_subset_1(sK0(X1_52,X2_52,X0_52,X0_54,X1_54),u1_struct_0(X2_52))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2628,plain,
    ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_54,X0_52),X1_54) = iProver_top
    | v1_funct_2(X1_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(sK0(X1_52,X2_52,X0_52,X0_54,X1_54),u1_struct_0(X2_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2043])).

cnf(c_7183,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7175,c_2628])).

cnf(c_7282,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7183,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_2876,c_3151,c_3686])).

cnf(c_7283,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_7282])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2061,plain,
    ( ~ m1_subset_1(X0_54,X0_53)
    | r2_hidden(X0_54,X0_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2610,plain,
    ( m1_subset_1(X0_54,X0_53) != iProver_top
    | r2_hidden(X0_54,X0_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2061])).

cnf(c_7288,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7283,c_2610])).

cnf(c_7299,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7184,c_36,c_37,c_38,c_2742,c_2876,c_7288])).

cnf(c_7300,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_7299])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2040,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_subset_1(X0_54,u1_struct_0(X1_52))
    | ~ r2_hidden(X0_54,u1_struct_0(X0_52))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52)
    | k1_funct_1(k4_tmap_1(X1_52,X0_52),X0_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2631,plain,
    ( k1_funct_1(k4_tmap_1(X0_52,X1_52),X0_54) = X0_54
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_52)) != iProver_top
    | r2_hidden(X0_54,u1_struct_0(X1_52)) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2040])).

cnf(c_7303,plain,
    ( k1_funct_1(k4_tmap_1(X0_52,sK2),sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_7300,c_2631])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2055,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_subset_1(X0_54,u1_struct_0(X0_52))
    | m1_subset_1(X0_54,u1_struct_0(X1_52))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2616,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2055])).

cnf(c_7287,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(X0_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_7283,c_2616])).

cnf(c_9160,plain,
    ( v2_struct_0(X0_52) = iProver_top
    | k1_funct_1(k4_tmap_1(X0_52,sK2),sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7303,c_37,c_7287])).

cnf(c_9161,plain,
    ( k1_funct_1(k4_tmap_1(X0_52,sK2),sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_9160])).

cnf(c_9165,plain,
    ( k1_funct_1(k4_tmap_1(X0_52,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_9161])).

cnf(c_9168,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9165])).

cnf(c_7829,plain,
    ( v2_struct_0(X0_52) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(X0_52)) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7287,c_37])).

cnf(c_7830,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(X0_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_7829])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,u1_struct_0(sK2))
    | k1_funct_1(sK3,X0) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2038,negated_conjecture,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK1))
    | ~ r2_hidden(X0_54,u1_struct_0(sK2))
    | k1_funct_1(sK3,X0_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2633,plain,
    ( k1_funct_1(sK3,X0_54) = X0_54
    | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_54,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2038])).

cnf(c_7833,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_7830,c_2633])).

cnf(c_7867,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7833,c_34,c_36,c_37,c_38,c_2742,c_2876,c_7288])).

cnf(c_7868,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_7867])).

cnf(c_7872,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_7868])).

cnf(c_24,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_45,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2063,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_2080,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2063])).

cnf(c_2071,plain,
    ( ~ r2_funct_2(X0_53,X1_53,X0_54,X1_54)
    | r2_funct_2(X0_53,X1_53,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_2792,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,X1_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
    | k4_tmap_1(sK1,sK2) != X0_54
    | sK3 != X1_54 ),
    inference(instantiation,[status(thm)],[c_2071])).

cnf(c_2793,plain,
    ( k4_tmap_1(sK1,sK2) != X0_54
    | sK3 != X1_54
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,X1_54) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2792])).

cnf(c_2795,plain,
    ( k4_tmap_1(sK1,sK2) != sK3
    | sK3 != sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2793])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2047,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52)
    | v1_funct_1(k4_tmap_1(X1_52,X0_52)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3194,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2047])).

cnf(c_3195,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3194])).

cnf(c_2,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2059,plain,
    ( r2_funct_2(X0_53,X1_53,X0_54,X0_54)
    | ~ v1_funct_2(X0_54,X0_53,X1_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2612,plain,
    ( r2_funct_2(X0_53,X1_53,X0_54,X0_54) = iProver_top
    | v1_funct_2(X0_54,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2059])).

cnf(c_3604,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_2612])).

cnf(c_15,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2048,plain,
    ( v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52))
    | ~ m1_pre_topc(X1_52,X0_52)
    | v2_struct_0(X0_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_4580,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2048])).

cnf(c_4581,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4580])).

cnf(c_2878,plain,
    ( ~ r2_funct_2(X0_53,X1_53,X0_54,k4_tmap_1(sK1,sK2))
    | ~ v1_funct_2(X0_54,X0_53,X1_53)
    | ~ v1_funct_2(k4_tmap_1(sK1,sK2),X0_53,X1_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | k4_tmap_1(sK1,sK2) = X0_54 ),
    inference(instantiation,[status(thm)],[c_2058])).

cnf(c_4588,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,k4_tmap_1(sK1,sK2))
    | ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | k4_tmap_1(sK1,sK2) = X0_54 ),
    inference(instantiation,[status(thm)],[c_2878])).

cnf(c_4589,plain,
    ( k4_tmap_1(sK1,sK2) = X0_54
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4588])).

cnf(c_4591,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4589])).

cnf(c_5039,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2049])).

cnf(c_5040,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5039])).

cnf(c_7998,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7872,c_34,c_35,c_36,c_38,c_39,c_40,c_41,c_45,c_2080,c_2795,c_3195,c_3604,c_4581,c_4591,c_5040])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2060,plain,
    ( ~ v1_funct_2(X0_54,X0_53,X1_53)
    | ~ m1_subset_1(X1_54,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_54)
    | v1_xboole_0(X0_53)
    | k3_funct_2(X0_53,X1_53,X0_54,X1_54) = k1_funct_1(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2611,plain,
    ( k3_funct_2(X0_53,X1_53,X0_54,X1_54) = k1_funct_1(X0_54,X1_54)
    | v1_funct_2(X0_54,X0_53,X1_53) != iProver_top
    | m1_subset_1(X1_54,X0_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2060])).

cnf(c_3672,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = k1_funct_1(sK3,X0_54)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_2611])).

cnf(c_3794,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = k1_funct_1(sK3,X0_54)
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3672,c_36,c_37,c_38,c_39,c_40,c_2742,c_2876])).

cnf(c_5297,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_54,X1_54)) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_54,X1_54))
    | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),k2_tmap_1(sK2,X0_52,X0_54,X1_52),X1_54) = iProver_top
    | v1_funct_2(X1_54,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X1_52,sK2) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_2628,c_3794])).

cnf(c_6504,plain,
    ( v2_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | m1_pre_topc(X1_52,sK2) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(X1_54,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),k2_tmap_1(sK2,X0_52,X0_54,X1_52),X1_54) = iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_54,X1_54)) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_54,X1_54))
    | l1_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5297,c_35,c_36,c_37,c_38,c_2876,c_3151])).

cnf(c_6505,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_54,X1_54)) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_54,X1_54))
    | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),k2_tmap_1(sK2,X0_52,X0_54,X1_52),X1_54) = iProver_top
    | v1_funct_2(X1_54,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X1_52,sK2) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_6504])).

cnf(c_3921,plain,
    ( k4_tmap_1(X0_52,X1_52) = X0_54
    | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_54,k4_tmap_1(X0_52,X1_52)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_2613])).

cnf(c_2110,plain,
    ( v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) = iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2048])).

cnf(c_7029,plain,
    ( v1_funct_2(X0_54,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_54,k4_tmap_1(X0_52,X1_52)) != iProver_top
    | k4_tmap_1(X0_52,X1_52) = X0_54
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3921,c_2110])).

cnf(c_7030,plain,
    ( k4_tmap_1(X0_52,X1_52) = X0_54
    | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_54,k4_tmap_1(X0_52,X1_52)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7029])).

cnf(c_7039,plain,
    ( k2_tmap_1(sK2,X0_52,X0_54,X1_52) = k4_tmap_1(X0_52,X1_52)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_54,k4_tmap_1(X0_52,X1_52))) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_54,k4_tmap_1(X0_52,X1_52)))
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_52,X0_54,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X1_52,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_52,X0_54,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_52,X0_54,X1_52)) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6505,c_7030])).

cnf(c_7306,plain,
    ( v1_funct_2(k2_tmap_1(sK2,X0_52,X0_54,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_54,k4_tmap_1(X0_52,X1_52))) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_54,k4_tmap_1(X0_52,X1_52)))
    | k2_tmap_1(sK2,X0_52,X0_54,X1_52) = k4_tmap_1(X0_52,X1_52)
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X1_52,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_52,X0_54,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_52,X0_54,X1_52)) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7039,c_2110])).

cnf(c_7307,plain,
    ( k2_tmap_1(sK2,X0_52,X0_54,X1_52) = k4_tmap_1(X0_52,X1_52)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_54,k4_tmap_1(X0_52,X1_52))) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_54,k4_tmap_1(X0_52,X1_52)))
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_52,X0_54,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X1_52,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_52,X0_54,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_52,X0_54,X1_52)) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7306])).

cnf(c_7312,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = k4_tmap_1(sK1,sK2)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7175,c_7307])).

cnf(c_7313,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | k4_tmap_1(sK1,sK2) = sK3
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7312,c_7175])).

cnf(c_7185,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7175,c_6505])).

cnf(c_7270,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7185,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_2876,c_3686])).

cnf(c_7271,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_7270])).

cnf(c_7275,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2622,c_7271])).

cnf(c_7316,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7313,c_34,c_35,c_36,c_38,c_39,c_40,c_41,c_45,c_2080,c_2795,c_3195,c_3604,c_4581,c_4591,c_5040,c_7275])).

cnf(c_18,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4)
    | k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,sK0(X1,X2,X0,X3,X4)) != k1_funct_1(X4,sK0(X1,X2,X0,X3,X4)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2045,plain,
    ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_54,X0_52),X1_54)
    | ~ v1_funct_2(X1_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ v1_funct_2(X0_54,u1_struct_0(X2_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | k3_funct_2(u1_struct_0(X2_52),u1_struct_0(X1_52),X0_54,sK0(X1_52,X2_52,X0_52,X0_54,X1_54)) != k1_funct_1(X1_54,sK0(X1_52,X2_52,X0_52,X0_54,X1_54)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2626,plain,
    ( k3_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_54,sK0(X1_52,X0_52,X2_52,X0_54,X1_54)) != k1_funct_1(X1_54,sK0(X1_52,X0_52,X2_52,X0_54,X1_54))
    | r2_funct_2(u1_struct_0(X2_52),u1_struct_0(X1_52),k2_tmap_1(X0_52,X1_52,X0_54,X2_52),X1_54) = iProver_top
    | v1_funct_2(X1_54,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2045])).

cnf(c_7318,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7316,c_2626])).

cnf(c_7319,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7318,c_7175])).

cnf(c_7322,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7319,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_45,c_2080,c_2795,c_2876,c_3151,c_3195,c_3604,c_3686,c_4581,c_4591,c_5040])).

cnf(c_8000,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_7998,c_7322])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9168,c_8000,c_5040,c_4591,c_4581,c_3604,c_3195,c_2795,c_2080,c_45,c_41,c_40,c_39,c_38,c_36,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:40:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.23/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.23/1.48  
% 7.23/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.23/1.48  
% 7.23/1.48  ------  iProver source info
% 7.23/1.48  
% 7.23/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.23/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.23/1.48  git: non_committed_changes: false
% 7.23/1.48  git: last_make_outside_of_git: false
% 7.23/1.48  
% 7.23/1.48  ------ 
% 7.23/1.48  
% 7.23/1.48  ------ Input Options
% 7.23/1.48  
% 7.23/1.48  --out_options                           all
% 7.23/1.48  --tptp_safe_out                         true
% 7.23/1.48  --problem_path                          ""
% 7.23/1.48  --include_path                          ""
% 7.23/1.48  --clausifier                            res/vclausify_rel
% 7.23/1.48  --clausifier_options                    ""
% 7.23/1.48  --stdin                                 false
% 7.23/1.48  --stats_out                             all
% 7.23/1.48  
% 7.23/1.48  ------ General Options
% 7.23/1.48  
% 7.23/1.48  --fof                                   false
% 7.23/1.48  --time_out_real                         305.
% 7.23/1.48  --time_out_virtual                      -1.
% 7.23/1.48  --symbol_type_check                     false
% 7.23/1.48  --clausify_out                          false
% 7.23/1.48  --sig_cnt_out                           false
% 7.23/1.48  --trig_cnt_out                          false
% 7.23/1.48  --trig_cnt_out_tolerance                1.
% 7.23/1.48  --trig_cnt_out_sk_spl                   false
% 7.23/1.48  --abstr_cl_out                          false
% 7.23/1.48  
% 7.23/1.48  ------ Global Options
% 7.23/1.48  
% 7.23/1.48  --schedule                              default
% 7.23/1.48  --add_important_lit                     false
% 7.23/1.48  --prop_solver_per_cl                    1000
% 7.23/1.48  --min_unsat_core                        false
% 7.23/1.48  --soft_assumptions                      false
% 7.23/1.48  --soft_lemma_size                       3
% 7.23/1.48  --prop_impl_unit_size                   0
% 7.23/1.48  --prop_impl_unit                        []
% 7.23/1.48  --share_sel_clauses                     true
% 7.23/1.48  --reset_solvers                         false
% 7.23/1.48  --bc_imp_inh                            [conj_cone]
% 7.23/1.48  --conj_cone_tolerance                   3.
% 7.23/1.48  --extra_neg_conj                        none
% 7.23/1.48  --large_theory_mode                     true
% 7.23/1.48  --prolific_symb_bound                   200
% 7.23/1.48  --lt_threshold                          2000
% 7.23/1.48  --clause_weak_htbl                      true
% 7.23/1.48  --gc_record_bc_elim                     false
% 7.23/1.48  
% 7.23/1.48  ------ Preprocessing Options
% 7.23/1.48  
% 7.23/1.48  --preprocessing_flag                    true
% 7.23/1.48  --time_out_prep_mult                    0.1
% 7.23/1.48  --splitting_mode                        input
% 7.23/1.48  --splitting_grd                         true
% 7.23/1.48  --splitting_cvd                         false
% 7.23/1.48  --splitting_cvd_svl                     false
% 7.23/1.48  --splitting_nvd                         32
% 7.23/1.48  --sub_typing                            true
% 7.23/1.48  --prep_gs_sim                           true
% 7.23/1.48  --prep_unflatten                        true
% 7.23/1.48  --prep_res_sim                          true
% 7.23/1.48  --prep_upred                            true
% 7.23/1.48  --prep_sem_filter                       exhaustive
% 7.23/1.48  --prep_sem_filter_out                   false
% 7.23/1.48  --pred_elim                             true
% 7.23/1.48  --res_sim_input                         true
% 7.23/1.48  --eq_ax_congr_red                       true
% 7.23/1.48  --pure_diseq_elim                       true
% 7.23/1.48  --brand_transform                       false
% 7.23/1.48  --non_eq_to_eq                          false
% 7.23/1.48  --prep_def_merge                        true
% 7.23/1.48  --prep_def_merge_prop_impl              false
% 7.23/1.48  --prep_def_merge_mbd                    true
% 7.23/1.48  --prep_def_merge_tr_red                 false
% 7.23/1.48  --prep_def_merge_tr_cl                  false
% 7.23/1.48  --smt_preprocessing                     true
% 7.23/1.48  --smt_ac_axioms                         fast
% 7.23/1.48  --preprocessed_out                      false
% 7.23/1.48  --preprocessed_stats                    false
% 7.23/1.48  
% 7.23/1.48  ------ Abstraction refinement Options
% 7.23/1.48  
% 7.23/1.48  --abstr_ref                             []
% 7.23/1.48  --abstr_ref_prep                        false
% 7.23/1.48  --abstr_ref_until_sat                   false
% 7.23/1.48  --abstr_ref_sig_restrict                funpre
% 7.23/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.23/1.48  --abstr_ref_under                       []
% 7.23/1.48  
% 7.23/1.48  ------ SAT Options
% 7.23/1.48  
% 7.23/1.48  --sat_mode                              false
% 7.23/1.48  --sat_fm_restart_options                ""
% 7.23/1.48  --sat_gr_def                            false
% 7.23/1.48  --sat_epr_types                         true
% 7.23/1.48  --sat_non_cyclic_types                  false
% 7.23/1.48  --sat_finite_models                     false
% 7.23/1.48  --sat_fm_lemmas                         false
% 7.23/1.48  --sat_fm_prep                           false
% 7.23/1.48  --sat_fm_uc_incr                        true
% 7.23/1.48  --sat_out_model                         small
% 7.23/1.48  --sat_out_clauses                       false
% 7.23/1.48  
% 7.23/1.48  ------ QBF Options
% 7.23/1.48  
% 7.23/1.48  --qbf_mode                              false
% 7.23/1.48  --qbf_elim_univ                         false
% 7.23/1.48  --qbf_dom_inst                          none
% 7.23/1.48  --qbf_dom_pre_inst                      false
% 7.23/1.48  --qbf_sk_in                             false
% 7.23/1.48  --qbf_pred_elim                         true
% 7.23/1.48  --qbf_split                             512
% 7.23/1.48  
% 7.23/1.48  ------ BMC1 Options
% 7.23/1.48  
% 7.23/1.48  --bmc1_incremental                      false
% 7.23/1.48  --bmc1_axioms                           reachable_all
% 7.23/1.48  --bmc1_min_bound                        0
% 7.23/1.48  --bmc1_max_bound                        -1
% 7.23/1.48  --bmc1_max_bound_default                -1
% 7.23/1.48  --bmc1_symbol_reachability              true
% 7.23/1.48  --bmc1_property_lemmas                  false
% 7.23/1.48  --bmc1_k_induction                      false
% 7.23/1.48  --bmc1_non_equiv_states                 false
% 7.23/1.48  --bmc1_deadlock                         false
% 7.23/1.48  --bmc1_ucm                              false
% 7.23/1.48  --bmc1_add_unsat_core                   none
% 7.23/1.48  --bmc1_unsat_core_children              false
% 7.23/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.23/1.48  --bmc1_out_stat                         full
% 7.23/1.48  --bmc1_ground_init                      false
% 7.23/1.48  --bmc1_pre_inst_next_state              false
% 7.23/1.48  --bmc1_pre_inst_state                   false
% 7.23/1.48  --bmc1_pre_inst_reach_state             false
% 7.23/1.48  --bmc1_out_unsat_core                   false
% 7.23/1.48  --bmc1_aig_witness_out                  false
% 7.23/1.48  --bmc1_verbose                          false
% 7.23/1.48  --bmc1_dump_clauses_tptp                false
% 7.23/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.23/1.48  --bmc1_dump_file                        -
% 7.23/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.23/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.23/1.48  --bmc1_ucm_extend_mode                  1
% 7.23/1.48  --bmc1_ucm_init_mode                    2
% 7.23/1.48  --bmc1_ucm_cone_mode                    none
% 7.23/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.23/1.48  --bmc1_ucm_relax_model                  4
% 7.23/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.23/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.23/1.48  --bmc1_ucm_layered_model                none
% 7.23/1.48  --bmc1_ucm_max_lemma_size               10
% 7.23/1.48  
% 7.23/1.48  ------ AIG Options
% 7.23/1.48  
% 7.23/1.48  --aig_mode                              false
% 7.23/1.48  
% 7.23/1.48  ------ Instantiation Options
% 7.23/1.48  
% 7.23/1.48  --instantiation_flag                    true
% 7.23/1.48  --inst_sos_flag                         true
% 7.23/1.48  --inst_sos_phase                        true
% 7.23/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.23/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.23/1.48  --inst_lit_sel_side                     num_symb
% 7.23/1.48  --inst_solver_per_active                1400
% 7.23/1.48  --inst_solver_calls_frac                1.
% 7.23/1.48  --inst_passive_queue_type               priority_queues
% 7.23/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.23/1.48  --inst_passive_queues_freq              [25;2]
% 7.23/1.48  --inst_dismatching                      true
% 7.23/1.48  --inst_eager_unprocessed_to_passive     true
% 7.23/1.48  --inst_prop_sim_given                   true
% 7.23/1.48  --inst_prop_sim_new                     false
% 7.23/1.48  --inst_subs_new                         false
% 7.23/1.48  --inst_eq_res_simp                      false
% 7.23/1.48  --inst_subs_given                       false
% 7.23/1.48  --inst_orphan_elimination               true
% 7.23/1.48  --inst_learning_loop_flag               true
% 7.23/1.48  --inst_learning_start                   3000
% 7.23/1.48  --inst_learning_factor                  2
% 7.23/1.48  --inst_start_prop_sim_after_learn       3
% 7.23/1.48  --inst_sel_renew                        solver
% 7.23/1.48  --inst_lit_activity_flag                true
% 7.23/1.48  --inst_restr_to_given                   false
% 7.23/1.48  --inst_activity_threshold               500
% 7.23/1.48  --inst_out_proof                        true
% 7.23/1.48  
% 7.23/1.48  ------ Resolution Options
% 7.23/1.48  
% 7.23/1.48  --resolution_flag                       true
% 7.23/1.48  --res_lit_sel                           adaptive
% 7.23/1.48  --res_lit_sel_side                      none
% 7.23/1.48  --res_ordering                          kbo
% 7.23/1.48  --res_to_prop_solver                    active
% 7.23/1.48  --res_prop_simpl_new                    false
% 7.23/1.48  --res_prop_simpl_given                  true
% 7.23/1.48  --res_passive_queue_type                priority_queues
% 7.23/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.23/1.48  --res_passive_queues_freq               [15;5]
% 7.23/1.48  --res_forward_subs                      full
% 7.23/1.48  --res_backward_subs                     full
% 7.23/1.48  --res_forward_subs_resolution           true
% 7.23/1.48  --res_backward_subs_resolution          true
% 7.23/1.48  --res_orphan_elimination                true
% 7.23/1.48  --res_time_limit                        2.
% 7.23/1.48  --res_out_proof                         true
% 7.23/1.48  
% 7.23/1.48  ------ Superposition Options
% 7.23/1.48  
% 7.23/1.48  --superposition_flag                    true
% 7.23/1.48  --sup_passive_queue_type                priority_queues
% 7.23/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.23/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.23/1.48  --demod_completeness_check              fast
% 7.23/1.48  --demod_use_ground                      true
% 7.23/1.48  --sup_to_prop_solver                    passive
% 7.23/1.48  --sup_prop_simpl_new                    true
% 7.23/1.48  --sup_prop_simpl_given                  true
% 7.23/1.48  --sup_fun_splitting                     true
% 7.23/1.48  --sup_smt_interval                      50000
% 7.23/1.48  
% 7.23/1.48  ------ Superposition Simplification Setup
% 7.23/1.48  
% 7.23/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.23/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.23/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.23/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.23/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.23/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.23/1.48  --sup_immed_triv                        [TrivRules]
% 7.23/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.23/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.23/1.48  --sup_immed_bw_main                     []
% 7.23/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.23/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.23/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.23/1.48  --sup_input_bw                          []
% 7.23/1.48  
% 7.23/1.48  ------ Combination Options
% 7.23/1.48  
% 7.23/1.48  --comb_res_mult                         3
% 7.23/1.48  --comb_sup_mult                         2
% 7.23/1.48  --comb_inst_mult                        10
% 7.23/1.48  
% 7.23/1.48  ------ Debug Options
% 7.23/1.48  
% 7.23/1.48  --dbg_backtrace                         false
% 7.23/1.48  --dbg_dump_prop_clauses                 false
% 7.23/1.48  --dbg_dump_prop_clauses_file            -
% 7.23/1.48  --dbg_out_stat                          false
% 7.23/1.48  ------ Parsing...
% 7.23/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.23/1.48  
% 7.23/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.23/1.48  
% 7.23/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.23/1.48  
% 7.23/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.23/1.48  ------ Proving...
% 7.23/1.48  ------ Problem Properties 
% 7.23/1.48  
% 7.23/1.48  
% 7.23/1.48  clauses                                 33
% 7.23/1.48  conjectures                             10
% 7.23/1.48  EPR                                     11
% 7.23/1.48  Horn                                    17
% 7.23/1.48  unary                                   9
% 7.23/1.48  binary                                  1
% 7.23/1.48  lits                                    199
% 7.23/1.48  lits eq                                 7
% 7.23/1.48  fd_pure                                 0
% 7.23/1.48  fd_pseudo                               0
% 7.23/1.48  fd_cond                                 0
% 7.23/1.48  fd_pseudo_cond                          1
% 7.23/1.48  AC symbols                              0
% 7.23/1.48  
% 7.23/1.48  ------ Schedule dynamic 5 is on 
% 7.23/1.48  
% 7.23/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.23/1.48  
% 7.23/1.48  
% 7.23/1.48  ------ 
% 7.23/1.48  Current options:
% 7.23/1.48  ------ 
% 7.23/1.48  
% 7.23/1.48  ------ Input Options
% 7.23/1.48  
% 7.23/1.48  --out_options                           all
% 7.23/1.48  --tptp_safe_out                         true
% 7.23/1.48  --problem_path                          ""
% 7.23/1.48  --include_path                          ""
% 7.23/1.48  --clausifier                            res/vclausify_rel
% 7.23/1.48  --clausifier_options                    ""
% 7.23/1.48  --stdin                                 false
% 7.23/1.48  --stats_out                             all
% 7.23/1.48  
% 7.23/1.48  ------ General Options
% 7.23/1.48  
% 7.23/1.48  --fof                                   false
% 7.23/1.48  --time_out_real                         305.
% 7.23/1.48  --time_out_virtual                      -1.
% 7.23/1.48  --symbol_type_check                     false
% 7.23/1.48  --clausify_out                          false
% 7.23/1.48  --sig_cnt_out                           false
% 7.23/1.48  --trig_cnt_out                          false
% 7.23/1.48  --trig_cnt_out_tolerance                1.
% 7.23/1.48  --trig_cnt_out_sk_spl                   false
% 7.23/1.48  --abstr_cl_out                          false
% 7.23/1.48  
% 7.23/1.48  ------ Global Options
% 7.23/1.48  
% 7.23/1.48  --schedule                              default
% 7.23/1.48  --add_important_lit                     false
% 7.23/1.48  --prop_solver_per_cl                    1000
% 7.23/1.48  --min_unsat_core                        false
% 7.23/1.48  --soft_assumptions                      false
% 7.23/1.48  --soft_lemma_size                       3
% 7.23/1.48  --prop_impl_unit_size                   0
% 7.23/1.48  --prop_impl_unit                        []
% 7.23/1.48  --share_sel_clauses                     true
% 7.23/1.48  --reset_solvers                         false
% 7.23/1.48  --bc_imp_inh                            [conj_cone]
% 7.23/1.48  --conj_cone_tolerance                   3.
% 7.23/1.48  --extra_neg_conj                        none
% 7.23/1.48  --large_theory_mode                     true
% 7.23/1.48  --prolific_symb_bound                   200
% 7.23/1.48  --lt_threshold                          2000
% 7.23/1.48  --clause_weak_htbl                      true
% 7.23/1.48  --gc_record_bc_elim                     false
% 7.23/1.48  
% 7.23/1.48  ------ Preprocessing Options
% 7.23/1.48  
% 7.23/1.48  --preprocessing_flag                    true
% 7.23/1.48  --time_out_prep_mult                    0.1
% 7.23/1.48  --splitting_mode                        input
% 7.23/1.48  --splitting_grd                         true
% 7.23/1.48  --splitting_cvd                         false
% 7.23/1.48  --splitting_cvd_svl                     false
% 7.23/1.48  --splitting_nvd                         32
% 7.23/1.48  --sub_typing                            true
% 7.23/1.48  --prep_gs_sim                           true
% 7.23/1.48  --prep_unflatten                        true
% 7.23/1.48  --prep_res_sim                          true
% 7.23/1.48  --prep_upred                            true
% 7.23/1.48  --prep_sem_filter                       exhaustive
% 7.23/1.48  --prep_sem_filter_out                   false
% 7.23/1.48  --pred_elim                             true
% 7.23/1.48  --res_sim_input                         true
% 7.23/1.48  --eq_ax_congr_red                       true
% 7.23/1.48  --pure_diseq_elim                       true
% 7.23/1.48  --brand_transform                       false
% 7.23/1.48  --non_eq_to_eq                          false
% 7.23/1.48  --prep_def_merge                        true
% 7.23/1.48  --prep_def_merge_prop_impl              false
% 7.23/1.48  --prep_def_merge_mbd                    true
% 7.23/1.48  --prep_def_merge_tr_red                 false
% 7.23/1.48  --prep_def_merge_tr_cl                  false
% 7.23/1.48  --smt_preprocessing                     true
% 7.23/1.48  --smt_ac_axioms                         fast
% 7.23/1.48  --preprocessed_out                      false
% 7.23/1.48  --preprocessed_stats                    false
% 7.23/1.48  
% 7.23/1.48  ------ Abstraction refinement Options
% 7.23/1.48  
% 7.23/1.48  --abstr_ref                             []
% 7.23/1.48  --abstr_ref_prep                        false
% 7.23/1.48  --abstr_ref_until_sat                   false
% 7.23/1.48  --abstr_ref_sig_restrict                funpre
% 7.23/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.23/1.48  --abstr_ref_under                       []
% 7.23/1.48  
% 7.23/1.48  ------ SAT Options
% 7.23/1.48  
% 7.23/1.48  --sat_mode                              false
% 7.23/1.48  --sat_fm_restart_options                ""
% 7.23/1.48  --sat_gr_def                            false
% 7.23/1.48  --sat_epr_types                         true
% 7.23/1.48  --sat_non_cyclic_types                  false
% 7.23/1.48  --sat_finite_models                     false
% 7.23/1.48  --sat_fm_lemmas                         false
% 7.23/1.48  --sat_fm_prep                           false
% 7.23/1.48  --sat_fm_uc_incr                        true
% 7.23/1.48  --sat_out_model                         small
% 7.23/1.48  --sat_out_clauses                       false
% 7.23/1.48  
% 7.23/1.48  ------ QBF Options
% 7.23/1.48  
% 7.23/1.48  --qbf_mode                              false
% 7.23/1.48  --qbf_elim_univ                         false
% 7.23/1.48  --qbf_dom_inst                          none
% 7.23/1.48  --qbf_dom_pre_inst                      false
% 7.23/1.48  --qbf_sk_in                             false
% 7.23/1.48  --qbf_pred_elim                         true
% 7.23/1.48  --qbf_split                             512
% 7.23/1.48  
% 7.23/1.48  ------ BMC1 Options
% 7.23/1.48  
% 7.23/1.48  --bmc1_incremental                      false
% 7.23/1.48  --bmc1_axioms                           reachable_all
% 7.23/1.48  --bmc1_min_bound                        0
% 7.23/1.48  --bmc1_max_bound                        -1
% 7.23/1.48  --bmc1_max_bound_default                -1
% 7.23/1.48  --bmc1_symbol_reachability              true
% 7.23/1.48  --bmc1_property_lemmas                  false
% 7.23/1.48  --bmc1_k_induction                      false
% 7.23/1.48  --bmc1_non_equiv_states                 false
% 7.23/1.48  --bmc1_deadlock                         false
% 7.23/1.48  --bmc1_ucm                              false
% 7.23/1.48  --bmc1_add_unsat_core                   none
% 7.23/1.48  --bmc1_unsat_core_children              false
% 7.23/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.23/1.48  --bmc1_out_stat                         full
% 7.23/1.48  --bmc1_ground_init                      false
% 7.23/1.48  --bmc1_pre_inst_next_state              false
% 7.23/1.48  --bmc1_pre_inst_state                   false
% 7.23/1.48  --bmc1_pre_inst_reach_state             false
% 7.23/1.48  --bmc1_out_unsat_core                   false
% 7.23/1.48  --bmc1_aig_witness_out                  false
% 7.23/1.48  --bmc1_verbose                          false
% 7.23/1.48  --bmc1_dump_clauses_tptp                false
% 7.23/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.23/1.48  --bmc1_dump_file                        -
% 7.23/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.23/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.23/1.48  --bmc1_ucm_extend_mode                  1
% 7.23/1.48  --bmc1_ucm_init_mode                    2
% 7.23/1.48  --bmc1_ucm_cone_mode                    none
% 7.23/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.23/1.48  --bmc1_ucm_relax_model                  4
% 7.23/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.23/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.23/1.48  --bmc1_ucm_layered_model                none
% 7.23/1.48  --bmc1_ucm_max_lemma_size               10
% 7.23/1.48  
% 7.23/1.48  ------ AIG Options
% 7.23/1.48  
% 7.23/1.48  --aig_mode                              false
% 7.23/1.48  
% 7.23/1.48  ------ Instantiation Options
% 7.23/1.48  
% 7.23/1.48  --instantiation_flag                    true
% 7.23/1.48  --inst_sos_flag                         true
% 7.23/1.48  --inst_sos_phase                        true
% 7.23/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.23/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.23/1.48  --inst_lit_sel_side                     none
% 7.23/1.48  --inst_solver_per_active                1400
% 7.23/1.48  --inst_solver_calls_frac                1.
% 7.23/1.48  --inst_passive_queue_type               priority_queues
% 7.23/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.23/1.48  --inst_passive_queues_freq              [25;2]
% 7.23/1.48  --inst_dismatching                      true
% 7.23/1.48  --inst_eager_unprocessed_to_passive     true
% 7.23/1.48  --inst_prop_sim_given                   true
% 7.23/1.48  --inst_prop_sim_new                     false
% 7.23/1.48  --inst_subs_new                         false
% 7.23/1.48  --inst_eq_res_simp                      false
% 7.23/1.48  --inst_subs_given                       false
% 7.23/1.48  --inst_orphan_elimination               true
% 7.23/1.48  --inst_learning_loop_flag               true
% 7.23/1.48  --inst_learning_start                   3000
% 7.23/1.48  --inst_learning_factor                  2
% 7.23/1.48  --inst_start_prop_sim_after_learn       3
% 7.23/1.48  --inst_sel_renew                        solver
% 7.23/1.48  --inst_lit_activity_flag                true
% 7.23/1.48  --inst_restr_to_given                   false
% 7.23/1.48  --inst_activity_threshold               500
% 7.23/1.48  --inst_out_proof                        true
% 7.23/1.48  
% 7.23/1.48  ------ Resolution Options
% 7.23/1.48  
% 7.23/1.48  --resolution_flag                       false
% 7.23/1.48  --res_lit_sel                           adaptive
% 7.23/1.48  --res_lit_sel_side                      none
% 7.23/1.48  --res_ordering                          kbo
% 7.23/1.48  --res_to_prop_solver                    active
% 7.23/1.48  --res_prop_simpl_new                    false
% 7.23/1.48  --res_prop_simpl_given                  true
% 7.23/1.48  --res_passive_queue_type                priority_queues
% 7.23/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.23/1.48  --res_passive_queues_freq               [15;5]
% 7.23/1.48  --res_forward_subs                      full
% 7.23/1.48  --res_backward_subs                     full
% 7.23/1.48  --res_forward_subs_resolution           true
% 7.23/1.48  --res_backward_subs_resolution          true
% 7.23/1.48  --res_orphan_elimination                true
% 7.23/1.48  --res_time_limit                        2.
% 7.23/1.48  --res_out_proof                         true
% 7.23/1.48  
% 7.23/1.48  ------ Superposition Options
% 7.23/1.48  
% 7.23/1.48  --superposition_flag                    true
% 7.23/1.48  --sup_passive_queue_type                priority_queues
% 7.23/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.23/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.23/1.48  --demod_completeness_check              fast
% 7.23/1.48  --demod_use_ground                      true
% 7.23/1.48  --sup_to_prop_solver                    passive
% 7.23/1.48  --sup_prop_simpl_new                    true
% 7.23/1.48  --sup_prop_simpl_given                  true
% 7.23/1.48  --sup_fun_splitting                     true
% 7.23/1.48  --sup_smt_interval                      50000
% 7.23/1.48  
% 7.23/1.48  ------ Superposition Simplification Setup
% 7.23/1.48  
% 7.23/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.23/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.23/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.23/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.23/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.23/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.23/1.48  --sup_immed_triv                        [TrivRules]
% 7.23/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.23/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.23/1.48  --sup_immed_bw_main                     []
% 7.23/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.23/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.23/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.23/1.48  --sup_input_bw                          []
% 7.23/1.48  
% 7.23/1.48  ------ Combination Options
% 7.23/1.48  
% 7.23/1.48  --comb_res_mult                         3
% 7.23/1.48  --comb_sup_mult                         2
% 7.23/1.48  --comb_inst_mult                        10
% 7.23/1.48  
% 7.23/1.48  ------ Debug Options
% 7.23/1.48  
% 7.23/1.48  --dbg_backtrace                         false
% 7.23/1.48  --dbg_dump_prop_clauses                 false
% 7.23/1.48  --dbg_dump_prop_clauses_file            -
% 7.23/1.48  --dbg_out_stat                          false
% 7.23/1.48  
% 7.23/1.48  
% 7.23/1.48  
% 7.23/1.48  
% 7.23/1.48  ------ Proving...
% 7.23/1.48  
% 7.23/1.48  
% 7.23/1.48  % SZS status Theorem for theBenchmark.p
% 7.23/1.48  
% 7.23/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.23/1.48  
% 7.23/1.48  fof(f12,axiom,(
% 7.23/1.48    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 7.23/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.48  
% 7.23/1.48  fof(f40,plain,(
% 7.23/1.48    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.23/1.48    inference(ennf_transformation,[],[f12])).
% 7.23/1.48  
% 7.23/1.48  fof(f41,plain,(
% 7.23/1.48    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.23/1.48    inference(flattening,[],[f40])).
% 7.23/1.48  
% 7.23/1.48  fof(f76,plain,(
% 7.23/1.48    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.23/1.48    inference(cnf_transformation,[],[f41])).
% 7.23/1.48  
% 7.23/1.48  fof(f18,conjecture,(
% 7.23/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 7.23/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.48  
% 7.23/1.48  fof(f19,negated_conjecture,(
% 7.23/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 7.23/1.48    inference(negated_conjecture,[],[f18])).
% 7.23/1.48  
% 7.23/1.48  fof(f51,plain,(
% 7.23/1.48    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.23/1.48    inference(ennf_transformation,[],[f19])).
% 7.23/1.48  
% 7.23/1.48  fof(f52,plain,(
% 7.23/1.48    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.23/1.48    inference(flattening,[],[f51])).
% 7.23/1.48  
% 7.23/1.48  fof(f58,plain,(
% 7.23/1.48    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 7.23/1.48    introduced(choice_axiom,[])).
% 7.23/1.48  
% 7.23/1.48  fof(f57,plain,(
% 7.23/1.48    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k4_tmap_1(X0,sK2),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.23/1.48    introduced(choice_axiom,[])).
% 7.23/1.48  
% 7.23/1.48  fof(f56,plain,(
% 7.23/1.48    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK1),k4_tmap_1(sK1,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 7.23/1.48    introduced(choice_axiom,[])).
% 7.23/1.48  
% 7.23/1.48  fof(f59,plain,(
% 7.23/1.48    ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 7.23/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f52,f58,f57,f56])).
% 7.23/1.48  
% 7.23/1.48  fof(f88,plain,(
% 7.23/1.48    m1_pre_topc(sK2,sK1)),
% 7.23/1.48    inference(cnf_transformation,[],[f59])).
% 7.23/1.48  
% 7.23/1.48  fof(f91,plain,(
% 7.23/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 7.23/1.48    inference(cnf_transformation,[],[f59])).
% 7.23/1.48  
% 7.23/1.48  fof(f10,axiom,(
% 7.23/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 7.23/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.48  
% 7.23/1.48  fof(f36,plain,(
% 7.23/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.23/1.48    inference(ennf_transformation,[],[f10])).
% 7.23/1.48  
% 7.23/1.48  fof(f37,plain,(
% 7.23/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.23/1.48    inference(flattening,[],[f36])).
% 7.23/1.48  
% 7.23/1.48  fof(f70,plain,(
% 7.23/1.48    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.23/1.48    inference(cnf_transformation,[],[f37])).
% 7.23/1.48  
% 7.23/1.48  fof(f84,plain,(
% 7.23/1.48    ~v2_struct_0(sK1)),
% 7.23/1.48    inference(cnf_transformation,[],[f59])).
% 7.23/1.48  
% 7.23/1.48  fof(f85,plain,(
% 7.23/1.48    v2_pre_topc(sK1)),
% 7.23/1.48    inference(cnf_transformation,[],[f59])).
% 7.23/1.48  
% 7.23/1.48  fof(f86,plain,(
% 7.23/1.48    l1_pre_topc(sK1)),
% 7.23/1.48    inference(cnf_transformation,[],[f59])).
% 7.23/1.48  
% 7.23/1.48  fof(f89,plain,(
% 7.23/1.48    v1_funct_1(sK3)),
% 7.23/1.48    inference(cnf_transformation,[],[f59])).
% 7.23/1.48  
% 7.23/1.48  fof(f90,plain,(
% 7.23/1.48    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 7.23/1.48    inference(cnf_transformation,[],[f59])).
% 7.23/1.48  
% 7.23/1.48  fof(f13,axiom,(
% 7.23/1.48    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.23/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.48  
% 7.23/1.48  fof(f42,plain,(
% 7.23/1.48    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.23/1.48    inference(ennf_transformation,[],[f13])).
% 7.23/1.48  
% 7.23/1.48  fof(f77,plain,(
% 7.23/1.48    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.23/1.48    inference(cnf_transformation,[],[f42])).
% 7.23/1.48  
% 7.23/1.48  fof(f9,axiom,(
% 7.23/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 7.23/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.48  
% 7.23/1.48  fof(f34,plain,(
% 7.23/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.23/1.48    inference(ennf_transformation,[],[f9])).
% 7.23/1.48  
% 7.23/1.48  fof(f35,plain,(
% 7.23/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.23/1.48    inference(flattening,[],[f34])).
% 7.23/1.48  
% 7.23/1.48  fof(f69,plain,(
% 7.23/1.48    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.23/1.48    inference(cnf_transformation,[],[f35])).
% 7.23/1.48  
% 7.23/1.48  fof(f87,plain,(
% 7.23/1.48    ~v2_struct_0(sK2)),
% 7.23/1.48    inference(cnf_transformation,[],[f59])).
% 7.23/1.48  
% 7.23/1.48  fof(f6,axiom,(
% 7.23/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.23/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.48  
% 7.23/1.48  fof(f29,plain,(
% 7.23/1.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.23/1.48    inference(ennf_transformation,[],[f6])).
% 7.23/1.48  
% 7.23/1.48  fof(f66,plain,(
% 7.23/1.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.23/1.48    inference(cnf_transformation,[],[f29])).
% 7.23/1.48  
% 7.23/1.48  fof(f4,axiom,(
% 7.23/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 7.23/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.48  
% 7.23/1.48  fof(f26,plain,(
% 7.23/1.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.23/1.48    inference(ennf_transformation,[],[f4])).
% 7.23/1.48  
% 7.23/1.48  fof(f27,plain,(
% 7.23/1.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.23/1.48    inference(flattening,[],[f26])).
% 7.23/1.48  
% 7.23/1.48  fof(f64,plain,(
% 7.23/1.48    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.23/1.48    inference(cnf_transformation,[],[f27])).
% 7.23/1.48  
% 7.23/1.48  fof(f11,axiom,(
% 7.23/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 7.23/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.48  
% 7.23/1.48  fof(f38,plain,(
% 7.23/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.23/1.48    inference(ennf_transformation,[],[f11])).
% 7.23/1.48  
% 7.23/1.48  fof(f39,plain,(
% 7.23/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.23/1.48    inference(flattening,[],[f38])).
% 7.23/1.48  
% 7.23/1.48  fof(f73,plain,(
% 7.23/1.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.23/1.48    inference(cnf_transformation,[],[f39])).
% 7.23/1.48  
% 7.23/1.48  fof(f3,axiom,(
% 7.23/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 7.23/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.48  
% 7.23/1.48  fof(f24,plain,(
% 7.23/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.23/1.48    inference(ennf_transformation,[],[f3])).
% 7.23/1.48  
% 7.23/1.48  fof(f25,plain,(
% 7.23/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.23/1.48    inference(flattening,[],[f24])).
% 7.23/1.48  
% 7.23/1.48  fof(f53,plain,(
% 7.23/1.48    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.23/1.48    inference(nnf_transformation,[],[f25])).
% 7.23/1.48  
% 7.23/1.48  fof(f62,plain,(
% 7.23/1.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.23/1.48    inference(cnf_transformation,[],[f53])).
% 7.23/1.48  
% 7.23/1.48  fof(f15,axiom,(
% 7.23/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 7.23/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.48  
% 7.23/1.48  fof(f45,plain,(
% 7.23/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.23/1.48    inference(ennf_transformation,[],[f15])).
% 7.23/1.48  
% 7.23/1.48  fof(f46,plain,(
% 7.23/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.23/1.48    inference(flattening,[],[f45])).
% 7.23/1.48  
% 7.23/1.48  fof(f81,plain,(
% 7.23/1.48    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.23/1.48    inference(cnf_transformation,[],[f46])).
% 7.23/1.48  
% 7.23/1.48  fof(f72,plain,(
% 7.23/1.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.23/1.48    inference(cnf_transformation,[],[f39])).
% 7.23/1.48  
% 7.23/1.48  fof(f71,plain,(
% 7.23/1.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.23/1.48    inference(cnf_transformation,[],[f39])).
% 7.23/1.48  
% 7.23/1.48  fof(f14,axiom,(
% 7.23/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 7.23/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.48  
% 7.23/1.48  fof(f43,plain,(
% 7.23/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.23/1.48    inference(ennf_transformation,[],[f14])).
% 7.23/1.48  
% 7.23/1.48  fof(f44,plain,(
% 7.23/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.23/1.48    inference(flattening,[],[f43])).
% 7.23/1.48  
% 7.23/1.48  fof(f54,plain,(
% 7.23/1.48    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) => (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))))),
% 7.23/1.48    introduced(choice_axiom,[])).
% 7.23/1.48  
% 7.23/1.48  fof(f55,plain,(
% 7.23/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.23/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f54])).
% 7.23/1.48  
% 7.23/1.48  fof(f79,plain,(
% 7.23/1.48    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.23/1.48    inference(cnf_transformation,[],[f55])).
% 7.23/1.48  
% 7.23/1.48  fof(f5,axiom,(
% 7.23/1.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.23/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.48  
% 7.23/1.48  fof(f28,plain,(
% 7.23/1.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.23/1.48    inference(ennf_transformation,[],[f5])).
% 7.23/1.48  
% 7.23/1.48  fof(f65,plain,(
% 7.23/1.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.23/1.48    inference(cnf_transformation,[],[f28])).
% 7.23/1.48  
% 7.23/1.48  fof(f7,axiom,(
% 7.23/1.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 7.23/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.48  
% 7.23/1.48  fof(f30,plain,(
% 7.23/1.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.23/1.48    inference(ennf_transformation,[],[f7])).
% 7.23/1.48  
% 7.23/1.48  fof(f31,plain,(
% 7.23/1.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.23/1.48    inference(flattening,[],[f30])).
% 7.23/1.48  
% 7.23/1.48  fof(f67,plain,(
% 7.23/1.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.23/1.48    inference(cnf_transformation,[],[f31])).
% 7.23/1.48  
% 7.23/1.48  fof(f78,plain,(
% 7.23/1.48    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.23/1.48    inference(cnf_transformation,[],[f55])).
% 7.23/1.48  
% 7.23/1.48  fof(f1,axiom,(
% 7.23/1.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.23/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.48  
% 7.23/1.48  fof(f20,plain,(
% 7.23/1.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.23/1.48    inference(ennf_transformation,[],[f1])).
% 7.23/1.48  
% 7.23/1.48  fof(f21,plain,(
% 7.23/1.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.23/1.48    inference(flattening,[],[f20])).
% 7.23/1.48  
% 7.23/1.48  fof(f60,plain,(
% 7.23/1.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.23/1.48    inference(cnf_transformation,[],[f21])).
% 7.23/1.49  
% 7.23/1.49  fof(f17,axiom,(
% 7.23/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f49,plain,(
% 7.23/1.49    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.23/1.49    inference(ennf_transformation,[],[f17])).
% 7.23/1.49  
% 7.23/1.49  fof(f50,plain,(
% 7.23/1.49    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.23/1.49    inference(flattening,[],[f49])).
% 7.23/1.49  
% 7.23/1.49  fof(f83,plain,(
% 7.23/1.49    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f50])).
% 7.23/1.49  
% 7.23/1.49  fof(f8,axiom,(
% 7.23/1.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f32,plain,(
% 7.23/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.23/1.49    inference(ennf_transformation,[],[f8])).
% 7.23/1.49  
% 7.23/1.49  fof(f33,plain,(
% 7.23/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.23/1.49    inference(flattening,[],[f32])).
% 7.23/1.49  
% 7.23/1.49  fof(f68,plain,(
% 7.23/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f33])).
% 7.23/1.49  
% 7.23/1.49  fof(f92,plain,(
% 7.23/1.49    ( ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) )),
% 7.23/1.49    inference(cnf_transformation,[],[f59])).
% 7.23/1.49  
% 7.23/1.49  fof(f93,plain,(
% 7.23/1.49    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)),
% 7.23/1.49    inference(cnf_transformation,[],[f59])).
% 7.23/1.49  
% 7.23/1.49  fof(f74,plain,(
% 7.23/1.49    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f41])).
% 7.23/1.49  
% 7.23/1.49  fof(f63,plain,(
% 7.23/1.49    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f53])).
% 7.23/1.49  
% 7.23/1.49  fof(f94,plain,(
% 7.23/1.49    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.23/1.49    inference(equality_resolution,[],[f63])).
% 7.23/1.49  
% 7.23/1.49  fof(f75,plain,(
% 7.23/1.49    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f41])).
% 7.23/1.49  
% 7.23/1.49  fof(f2,axiom,(
% 7.23/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 7.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f22,plain,(
% 7.23/1.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 7.23/1.49    inference(ennf_transformation,[],[f2])).
% 7.23/1.49  
% 7.23/1.49  fof(f23,plain,(
% 7.23/1.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 7.23/1.49    inference(flattening,[],[f22])).
% 7.23/1.49  
% 7.23/1.49  fof(f61,plain,(
% 7.23/1.49    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f23])).
% 7.23/1.49  
% 7.23/1.49  fof(f80,plain,(
% 7.23/1.49    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f55])).
% 7.23/1.49  
% 7.23/1.49  cnf(c_14,plain,
% 7.23/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.23/1.49      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.23/1.49      | v2_struct_0(X1)
% 7.23/1.49      | ~ l1_pre_topc(X1)
% 7.23/1.49      | ~ v2_pre_topc(X1) ),
% 7.23/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2049,plain,
% 7.23/1.49      ( ~ m1_pre_topc(X0_52,X1_52)
% 7.23/1.49      | m1_subset_1(k4_tmap_1(X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 7.23/1.49      | v2_struct_0(X1_52)
% 7.23/1.49      | ~ l1_pre_topc(X1_52)
% 7.23/1.49      | ~ v2_pre_topc(X1_52) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2622,plain,
% 7.23/1.49      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 7.23/1.49      | m1_subset_1(k4_tmap_1(X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) = iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X1_52) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2049]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_29,negated_conjecture,
% 7.23/1.49      ( m1_pre_topc(sK2,sK1) ),
% 7.23/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2034,negated_conjecture,
% 7.23/1.49      ( m1_pre_topc(sK2,sK1) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_29]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2637,plain,
% 7.23/1.49      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2034]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_26,negated_conjecture,
% 7.23/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 7.23/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2037,negated_conjecture,
% 7.23/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_26]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2634,plain,
% 7.23/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2037]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_10,plain,
% 7.23/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.23/1.49      | ~ m1_pre_topc(X3,X4)
% 7.23/1.49      | ~ m1_pre_topc(X3,X1)
% 7.23/1.49      | ~ m1_pre_topc(X1,X4)
% 7.23/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.23/1.49      | v2_struct_0(X4)
% 7.23/1.49      | v2_struct_0(X2)
% 7.23/1.49      | ~ l1_pre_topc(X4)
% 7.23/1.49      | ~ l1_pre_topc(X2)
% 7.23/1.49      | ~ v2_pre_topc(X4)
% 7.23/1.49      | ~ v2_pre_topc(X2)
% 7.23/1.49      | ~ v1_funct_1(X0)
% 7.23/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 7.23/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2053,plain,
% 7.23/1.49      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 7.23/1.49      | ~ m1_pre_topc(X2_52,X0_52)
% 7.23/1.49      | ~ m1_pre_topc(X0_52,X3_52)
% 7.23/1.49      | ~ m1_pre_topc(X2_52,X3_52)
% 7.23/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 7.23/1.49      | v2_struct_0(X1_52)
% 7.23/1.49      | v2_struct_0(X3_52)
% 7.23/1.49      | ~ l1_pre_topc(X1_52)
% 7.23/1.49      | ~ l1_pre_topc(X3_52)
% 7.23/1.49      | ~ v2_pre_topc(X1_52)
% 7.23/1.49      | ~ v2_pre_topc(X3_52)
% 7.23/1.49      | ~ v1_funct_1(X0_54)
% 7.23/1.49      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_54,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_54) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2618,plain,
% 7.23/1.49      ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_54,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_54)
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 7.23/1.49      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 7.23/1.49      | m1_pre_topc(X2_52,X3_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X3_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | l1_pre_topc(X3_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X3_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2053]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5174,plain,
% 7.23/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK2,X0_52,sK3)
% 7.23/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 7.23/1.49      | m1_pre_topc(X0_52,sK2) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,X1_52) != iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_2634,c_2618]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_33,negated_conjecture,
% 7.23/1.49      ( ~ v2_struct_0(sK1) ),
% 7.23/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_34,plain,
% 7.23/1.49      ( v2_struct_0(sK1) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_32,negated_conjecture,
% 7.23/1.49      ( v2_pre_topc(sK1) ),
% 7.23/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_35,plain,
% 7.23/1.49      ( v2_pre_topc(sK1) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_31,negated_conjecture,
% 7.23/1.49      ( l1_pre_topc(sK1) ),
% 7.23/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_36,plain,
% 7.23/1.49      ( l1_pre_topc(sK1) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_28,negated_conjecture,
% 7.23/1.49      ( v1_funct_1(sK3) ),
% 7.23/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_39,plain,
% 7.23/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_27,negated_conjecture,
% 7.23/1.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 7.23/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_40,plain,
% 7.23/1.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5918,plain,
% 7.23/1.49      ( l1_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK2,X0_52,sK3)
% 7.23/1.49      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 7.23/1.49      | m1_pre_topc(X0_52,sK2) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,X1_52) != iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | v2_pre_topc(X1_52) != iProver_top ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_5174,c_34,c_35,c_36,c_39,c_40,c_41,c_2919]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5919,plain,
% 7.23/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK2,X0_52,sK3)
% 7.23/1.49      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 7.23/1.49      | m1_pre_topc(X0_52,sK2) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,X1_52) != iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X1_52) != iProver_top ),
% 7.23/1.49      inference(renaming,[status(thm)],[c_5918]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5924,plain,
% 7.23/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k3_tmap_1(sK1,sK1,sK2,sK2,sK3)
% 7.23/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_2637,c_5919]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_17,plain,
% 7.23/1.49      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.23/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2046,plain,
% 7.23/1.49      ( m1_pre_topc(X0_52,X0_52) | ~ l1_pre_topc(X0_52) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_17]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2625,plain,
% 7.23/1.49      ( m1_pre_topc(X0_52,X0_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2046]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_9,plain,
% 7.23/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.23/1.49      | ~ m1_pre_topc(X3,X1)
% 7.23/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.23/1.49      | v2_struct_0(X1)
% 7.23/1.49      | v2_struct_0(X2)
% 7.23/1.49      | ~ l1_pre_topc(X1)
% 7.23/1.49      | ~ l1_pre_topc(X2)
% 7.23/1.49      | ~ v2_pre_topc(X1)
% 7.23/1.49      | ~ v2_pre_topc(X2)
% 7.23/1.49      | ~ v1_funct_1(X0)
% 7.23/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.23/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2054,plain,
% 7.23/1.49      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 7.23/1.49      | ~ m1_pre_topc(X2_52,X0_52)
% 7.23/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 7.23/1.49      | v2_struct_0(X0_52)
% 7.23/1.49      | v2_struct_0(X1_52)
% 7.23/1.49      | ~ l1_pre_topc(X0_52)
% 7.23/1.49      | ~ l1_pre_topc(X1_52)
% 7.23/1.49      | ~ v2_pre_topc(X1_52)
% 7.23/1.49      | ~ v2_pre_topc(X0_52)
% 7.23/1.49      | ~ v1_funct_1(X0_54)
% 7.23/1.49      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_54,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_54,X2_52) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_9]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2617,plain,
% 7.23/1.49      ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_54,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_54,X2_52)
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2054]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4494,plain,
% 7.23/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_52)) = k2_tmap_1(sK2,sK1,sK3,X0_52)
% 7.23/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X0_52,sK2) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | v2_struct_0(sK2) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_2634,c_2617]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_30,negated_conjecture,
% 7.23/1.49      ( ~ v2_struct_0(sK2) ),
% 7.23/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_37,plain,
% 7.23/1.49      ( v2_struct_0(sK2) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_38,plain,
% 7.23/1.49      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_6,plain,
% 7.23/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.23/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2056,plain,
% 7.23/1.49      ( ~ m1_pre_topc(X0_52,X1_52)
% 7.23/1.49      | ~ l1_pre_topc(X1_52)
% 7.23/1.49      | l1_pre_topc(X0_52) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2873,plain,
% 7.23/1.49      ( ~ m1_pre_topc(sK2,X0_52)
% 7.23/1.49      | ~ l1_pre_topc(X0_52)
% 7.23/1.49      | l1_pre_topc(sK2) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2056]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2874,plain,
% 7.23/1.49      ( m1_pre_topc(sK2,X0_52) != iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | l1_pre_topc(sK2) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2873]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2876,plain,
% 7.23/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | l1_pre_topc(sK2) = iProver_top ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2874]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4,plain,
% 7.23/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.23/1.49      | ~ l1_pre_topc(X1)
% 7.23/1.49      | ~ v2_pre_topc(X1)
% 7.23/1.49      | v2_pre_topc(X0) ),
% 7.23/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2057,plain,
% 7.23/1.49      ( ~ m1_pre_topc(X0_52,X1_52)
% 7.23/1.49      | ~ l1_pre_topc(X1_52)
% 7.23/1.49      | ~ v2_pre_topc(X1_52)
% 7.23/1.49      | v2_pre_topc(X0_52) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3148,plain,
% 7.23/1.49      ( ~ m1_pre_topc(sK2,X0_52)
% 7.23/1.49      | ~ l1_pre_topc(X0_52)
% 7.23/1.49      | ~ v2_pre_topc(X0_52)
% 7.23/1.49      | v2_pre_topc(sK2) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2057]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3149,plain,
% 7.23/1.49      ( m1_pre_topc(sK2,X0_52) != iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK2) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_3148]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3151,plain,
% 7.23/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK2) = iProver_top ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_3149]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4964,plain,
% 7.23/1.49      ( m1_pre_topc(X0_52,sK2) != iProver_top
% 7.23/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_52)) = k2_tmap_1(sK2,sK1,sK3,X0_52) ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_4494,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_2876,c_3151]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4965,plain,
% 7.23/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_52)) = k2_tmap_1(sK2,sK1,sK3,X0_52)
% 7.23/1.49      | m1_pre_topc(X0_52,sK2) != iProver_top ),
% 7.23/1.49      inference(renaming,[status(thm)],[c_4964]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4970,plain,
% 7.23/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2)
% 7.23/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_2625,c_4965]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2875,plain,
% 7.23/1.49      ( ~ m1_pre_topc(sK2,sK1) | ~ l1_pre_topc(sK1) | l1_pre_topc(sK2) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2873]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3150,plain,
% 7.23/1.49      ( ~ m1_pre_topc(sK2,sK1)
% 7.23/1.49      | ~ l1_pre_topc(sK1)
% 7.23/1.49      | ~ v2_pre_topc(sK1)
% 7.23/1.49      | v2_pre_topc(sK2) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_3148]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3685,plain,
% 7.23/1.49      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2046]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2737,plain,
% 7.23/1.49      ( ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_52))
% 7.23/1.49      | ~ m1_pre_topc(X1_52,sK2)
% 7.23/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52))))
% 7.23/1.49      | v2_struct_0(X0_52)
% 7.23/1.49      | v2_struct_0(sK2)
% 7.23/1.49      | ~ l1_pre_topc(X0_52)
% 7.23/1.49      | ~ l1_pre_topc(sK2)
% 7.23/1.49      | ~ v2_pre_topc(X0_52)
% 7.23/1.49      | ~ v2_pre_topc(sK2)
% 7.23/1.49      | ~ v1_funct_1(X0_54)
% 7.23/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0_52),X0_54,u1_struct_0(X1_52)) = k2_tmap_1(sK2,X0_52,X0_54,X1_52) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2054]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3693,plain,
% 7.23/1.49      ( ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_52))
% 7.23/1.49      | ~ m1_pre_topc(sK2,sK2)
% 7.23/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52))))
% 7.23/1.49      | v2_struct_0(X0_52)
% 7.23/1.49      | v2_struct_0(sK2)
% 7.23/1.49      | ~ l1_pre_topc(X0_52)
% 7.23/1.49      | ~ l1_pre_topc(sK2)
% 7.23/1.49      | ~ v2_pre_topc(X0_52)
% 7.23/1.49      | ~ v2_pre_topc(sK2)
% 7.23/1.49      | ~ v1_funct_1(X0_54)
% 7.23/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X0_52),X0_54,u1_struct_0(sK2)) = k2_tmap_1(sK2,X0_52,X0_54,sK2) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2737]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3695,plain,
% 7.23/1.49      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.23/1.49      | ~ m1_pre_topc(sK2,sK2)
% 7.23/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.23/1.49      | v2_struct_0(sK1)
% 7.23/1.49      | v2_struct_0(sK2)
% 7.23/1.49      | ~ l1_pre_topc(sK1)
% 7.23/1.49      | ~ l1_pre_topc(sK2)
% 7.23/1.49      | ~ v2_pre_topc(sK1)
% 7.23/1.49      | ~ v2_pre_topc(sK2)
% 7.23/1.49      | ~ v1_funct_1(sK3)
% 7.23/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_3693]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5011,plain,
% 7.23/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_4970,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_2875,
% 7.23/1.49                 c_3150,c_3685,c_3695]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5926,plain,
% 7.23/1.49      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2)
% 7.23/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top ),
% 7.23/1.49      inference(light_normalisation,[status(thm)],[c_5924,c_5011]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3686,plain,
% 7.23/1.49      ( m1_pre_topc(sK2,sK2) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_3685]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_6150,plain,
% 7.23/1.49      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_5926,c_34,c_35,c_36,c_38,c_2876,c_3686]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_11,plain,
% 7.23/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.23/1.49      | ~ m1_pre_topc(X3,X4)
% 7.23/1.49      | ~ m1_pre_topc(X1,X4)
% 7.23/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.23/1.49      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 7.23/1.49      | v2_struct_0(X4)
% 7.23/1.49      | v2_struct_0(X2)
% 7.23/1.49      | ~ l1_pre_topc(X4)
% 7.23/1.49      | ~ l1_pre_topc(X2)
% 7.23/1.49      | ~ v2_pre_topc(X4)
% 7.23/1.49      | ~ v2_pre_topc(X2)
% 7.23/1.49      | ~ v1_funct_1(X0) ),
% 7.23/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2052,plain,
% 7.23/1.49      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 7.23/1.49      | ~ m1_pre_topc(X0_52,X2_52)
% 7.23/1.49      | ~ m1_pre_topc(X3_52,X2_52)
% 7.23/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 7.23/1.49      | m1_subset_1(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
% 7.23/1.49      | v2_struct_0(X1_52)
% 7.23/1.49      | v2_struct_0(X2_52)
% 7.23/1.49      | ~ l1_pre_topc(X1_52)
% 7.23/1.49      | ~ l1_pre_topc(X2_52)
% 7.23/1.49      | ~ v2_pre_topc(X1_52)
% 7.23/1.49      | ~ v2_pre_topc(X2_52)
% 7.23/1.49      | ~ v1_funct_1(X0_54) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2619,plain,
% 7.23/1.49      ( v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 7.23/1.49      | m1_pre_topc(X3_52,X2_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 7.23/1.49      | m1_subset_1(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52)))) = iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X2_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | l1_pre_topc(X2_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X2_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2052]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_6153,plain,
% 7.23/1.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | m1_subset_1(k2_tmap_1(sK2,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 7.23/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_6150,c_2619]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_41,plain,
% 7.23/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7144,plain,
% 7.23/1.49      ( m1_subset_1(k2_tmap_1(sK2,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_6153,c_34,c_35,c_36,c_38,c_39,c_40,c_41]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3,plain,
% 7.23/1.49      ( ~ r2_funct_2(X0,X1,X2,X3)
% 7.23/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.23/1.49      | ~ v1_funct_2(X3,X0,X1)
% 7.23/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.23/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.23/1.49      | ~ v1_funct_1(X2)
% 7.23/1.49      | ~ v1_funct_1(X3)
% 7.23/1.49      | X3 = X2 ),
% 7.23/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2058,plain,
% 7.23/1.49      ( ~ r2_funct_2(X0_53,X1_53,X0_54,X1_54)
% 7.23/1.49      | ~ v1_funct_2(X0_54,X0_53,X1_53)
% 7.23/1.49      | ~ v1_funct_2(X1_54,X0_53,X1_53)
% 7.23/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.23/1.49      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.23/1.49      | ~ v1_funct_1(X0_54)
% 7.23/1.49      | ~ v1_funct_1(X1_54)
% 7.23/1.49      | X1_54 = X0_54 ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2613,plain,
% 7.23/1.49      ( X0_54 = X1_54
% 7.23/1.49      | r2_funct_2(X0_53,X1_53,X1_54,X0_54) != iProver_top
% 7.23/1.49      | v1_funct_2(X1_54,X0_53,X1_53) != iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,X0_53,X1_53) != iProver_top
% 7.23/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.23/1.49      | v1_funct_1(X1_54) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2058]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3920,plain,
% 7.23/1.49      ( sK3 = X0_54
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,sK3) != iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_2634,c_2613]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3927,plain,
% 7.23/1.49      ( v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | sK3 = X0_54
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,sK3) != iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_3920,c_39,c_40]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3928,plain,
% 7.23/1.49      ( sK3 = X0_54
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,sK3) != iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(renaming,[status(thm)],[c_3927]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7155,plain,
% 7.23/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),sK3) != iProver_top
% 7.23/1.49      | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_7144,c_3928]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_21,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
% 7.23/1.49      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 7.23/1.49      | ~ m1_pre_topc(X0,X3)
% 7.23/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.23/1.49      | v2_struct_0(X3)
% 7.23/1.49      | v2_struct_0(X1)
% 7.23/1.49      | v2_struct_0(X0)
% 7.23/1.49      | ~ l1_pre_topc(X3)
% 7.23/1.49      | ~ l1_pre_topc(X1)
% 7.23/1.49      | ~ v2_pre_topc(X3)
% 7.23/1.49      | ~ v2_pre_topc(X1)
% 7.23/1.49      | ~ v1_funct_1(X2) ),
% 7.23/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2042,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_54,k3_tmap_1(X2_52,X1_52,X0_52,X0_52,X0_54))
% 7.23/1.49      | ~ v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 7.23/1.49      | ~ m1_pre_topc(X0_52,X2_52)
% 7.23/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 7.23/1.49      | v2_struct_0(X0_52)
% 7.23/1.49      | v2_struct_0(X1_52)
% 7.23/1.49      | v2_struct_0(X2_52)
% 7.23/1.49      | ~ l1_pre_topc(X1_52)
% 7.23/1.49      | ~ l1_pre_topc(X2_52)
% 7.23/1.49      | ~ v2_pre_topc(X1_52)
% 7.23/1.49      | ~ v2_pre_topc(X2_52)
% 7.23/1.49      | ~ v1_funct_1(X0_54) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_21]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2629,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_54,k3_tmap_1(X2_52,X1_52,X0_52,X0_52,X0_54)) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X2_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | l1_pre_topc(X2_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X2_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2042]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_6152,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top
% 7.23/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | v2_struct_0(sK2) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_6150,c_2629]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_12,plain,
% 7.23/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.23/1.49      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 7.23/1.49      | ~ m1_pre_topc(X4,X3)
% 7.23/1.49      | ~ m1_pre_topc(X1,X3)
% 7.23/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.23/1.49      | v2_struct_0(X3)
% 7.23/1.49      | v2_struct_0(X2)
% 7.23/1.49      | ~ l1_pre_topc(X3)
% 7.23/1.49      | ~ l1_pre_topc(X2)
% 7.23/1.49      | ~ v2_pre_topc(X3)
% 7.23/1.49      | ~ v2_pre_topc(X2)
% 7.23/1.49      | ~ v1_funct_1(X0) ),
% 7.23/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2051,plain,
% 7.23/1.49      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 7.23/1.49      | v1_funct_2(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_54),u1_struct_0(X3_52),u1_struct_0(X1_52))
% 7.23/1.49      | ~ m1_pre_topc(X0_52,X2_52)
% 7.23/1.49      | ~ m1_pre_topc(X3_52,X2_52)
% 7.23/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 7.23/1.49      | v2_struct_0(X1_52)
% 7.23/1.49      | v2_struct_0(X2_52)
% 7.23/1.49      | ~ l1_pre_topc(X1_52)
% 7.23/1.49      | ~ l1_pre_topc(X2_52)
% 7.23/1.49      | ~ v2_pre_topc(X1_52)
% 7.23/1.49      | ~ v2_pre_topc(X2_52)
% 7.23/1.49      | ~ v1_funct_1(X0_54) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_12]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2620,plain,
% 7.23/1.49      ( v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 7.23/1.49      | v1_funct_2(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_54),u1_struct_0(X3_52),u1_struct_0(X1_52)) = iProver_top
% 7.23/1.49      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 7.23/1.49      | m1_pre_topc(X3_52,X2_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X2_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | l1_pre_topc(X2_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X2_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2051]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_6154,plain,
% 7.23/1.49      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 7.23/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_6150,c_2620]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_13,plain,
% 7.23/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.23/1.49      | ~ m1_pre_topc(X3,X4)
% 7.23/1.49      | ~ m1_pre_topc(X1,X4)
% 7.23/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.23/1.49      | v2_struct_0(X4)
% 7.23/1.49      | v2_struct_0(X2)
% 7.23/1.49      | ~ l1_pre_topc(X4)
% 7.23/1.49      | ~ l1_pre_topc(X2)
% 7.23/1.49      | ~ v2_pre_topc(X4)
% 7.23/1.49      | ~ v2_pre_topc(X2)
% 7.23/1.49      | ~ v1_funct_1(X0)
% 7.23/1.49      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 7.23/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2050,plain,
% 7.23/1.49      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 7.23/1.49      | ~ m1_pre_topc(X0_52,X2_52)
% 7.23/1.49      | ~ m1_pre_topc(X3_52,X2_52)
% 7.23/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 7.23/1.49      | v2_struct_0(X1_52)
% 7.23/1.49      | v2_struct_0(X2_52)
% 7.23/1.49      | ~ l1_pre_topc(X1_52)
% 7.23/1.49      | ~ l1_pre_topc(X2_52)
% 7.23/1.49      | ~ v2_pre_topc(X1_52)
% 7.23/1.49      | ~ v2_pre_topc(X2_52)
% 7.23/1.49      | ~ v1_funct_1(X0_54)
% 7.23/1.49      | v1_funct_1(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_54)) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2621,plain,
% 7.23/1.49      ( v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 7.23/1.49      | m1_pre_topc(X3_52,X2_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X2_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | l1_pre_topc(X2_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X2_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_54)) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2050]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4503,plain,
% 7.23/1.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,X1_52) != iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v1_funct_1(k3_tmap_1(X1_52,sK1,sK2,X0_52,sK3)) = iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_2634,c_2621]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2713,plain,
% 7.23/1.49      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(sK1))
% 7.23/1.49      | ~ m1_pre_topc(X0_52,X1_52)
% 7.23/1.49      | ~ m1_pre_topc(X2_52,X1_52)
% 7.23/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1))))
% 7.23/1.49      | v2_struct_0(X1_52)
% 7.23/1.49      | v2_struct_0(sK1)
% 7.23/1.49      | ~ l1_pre_topc(X1_52)
% 7.23/1.49      | ~ l1_pre_topc(sK1)
% 7.23/1.49      | ~ v2_pre_topc(X1_52)
% 7.23/1.49      | ~ v2_pre_topc(sK1)
% 7.23/1.49      | ~ v1_funct_1(X0_54)
% 7.23/1.49      | v1_funct_1(k3_tmap_1(X1_52,sK1,X0_52,X2_52,X0_54)) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2050]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2819,plain,
% 7.23/1.49      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.23/1.49      | ~ m1_pre_topc(X0_52,X1_52)
% 7.23/1.49      | ~ m1_pre_topc(sK2,X1_52)
% 7.23/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.23/1.49      | v2_struct_0(X1_52)
% 7.23/1.49      | v2_struct_0(sK1)
% 7.23/1.49      | ~ l1_pre_topc(X1_52)
% 7.23/1.49      | ~ l1_pre_topc(sK1)
% 7.23/1.49      | ~ v2_pre_topc(X1_52)
% 7.23/1.49      | ~ v2_pre_topc(sK1)
% 7.23/1.49      | v1_funct_1(k3_tmap_1(X1_52,sK1,sK2,X0_52,sK3))
% 7.23/1.49      | ~ v1_funct_1(sK3) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2713]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2820,plain,
% 7.23/1.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,X1_52) != iProver_top
% 7.23/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v1_funct_1(k3_tmap_1(X1_52,sK1,sK2,X0_52,sK3)) = iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2819]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5004,plain,
% 7.23/1.49      ( v1_funct_1(k3_tmap_1(X1_52,sK1,sK2,X0_52,sK3)) = iProver_top
% 7.23/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,X1_52) != iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | v2_pre_topc(X1_52) != iProver_top ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_4503,c_34,c_35,c_36,c_39,c_40]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5005,plain,
% 7.23/1.49      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,X1_52) != iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | v1_funct_1(k3_tmap_1(X1_52,sK1,sK2,X0_52,sK3)) = iProver_top ),
% 7.23/1.49      inference(renaming,[status(thm)],[c_5004]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_6155,plain,
% 7.23/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_6150,c_5005]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7151,plain,
% 7.23/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = X0_54
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_7144,c_2613]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7166,plain,
% 7.23/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 7.23/1.49      | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_7151]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7175,plain,
% 7.23/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_7155,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_6152,
% 7.23/1.49                 c_6154,c_6155,c_7166]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_19,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 7.23/1.49      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 7.23/1.49      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 7.23/1.49      | ~ m1_pre_topc(X0,X2)
% 7.23/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.23/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 7.23/1.49      | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
% 7.23/1.49      | v2_struct_0(X1)
% 7.23/1.49      | v2_struct_0(X2)
% 7.23/1.49      | v2_struct_0(X0)
% 7.23/1.49      | ~ l1_pre_topc(X1)
% 7.23/1.49      | ~ l1_pre_topc(X2)
% 7.23/1.49      | ~ v2_pre_topc(X1)
% 7.23/1.49      | ~ v2_pre_topc(X2)
% 7.23/1.49      | ~ v1_funct_1(X3)
% 7.23/1.49      | ~ v1_funct_1(X4) ),
% 7.23/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2044,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_54,X0_52),X1_54)
% 7.23/1.49      | ~ v1_funct_2(X1_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 7.23/1.49      | ~ v1_funct_2(X0_54,u1_struct_0(X2_52),u1_struct_0(X1_52))
% 7.23/1.49      | ~ m1_pre_topc(X0_52,X2_52)
% 7.23/1.49      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 7.23/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 7.23/1.49      | r2_hidden(sK0(X1_52,X2_52,X0_52,X0_54,X1_54),u1_struct_0(X0_52))
% 7.23/1.49      | v2_struct_0(X0_52)
% 7.23/1.49      | v2_struct_0(X1_52)
% 7.23/1.49      | v2_struct_0(X2_52)
% 7.23/1.49      | ~ l1_pre_topc(X1_52)
% 7.23/1.49      | ~ l1_pre_topc(X2_52)
% 7.23/1.49      | ~ v2_pre_topc(X1_52)
% 7.23/1.49      | ~ v2_pre_topc(X2_52)
% 7.23/1.49      | ~ v1_funct_1(X0_54)
% 7.23/1.49      | ~ v1_funct_1(X1_54) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_19]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2627,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_54,X0_52),X1_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X1_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
% 7.23/1.49      | r2_hidden(sK0(X1_52,X2_52,X0_52,X0_54,X1_54),u1_struct_0(X0_52)) = iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X2_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | l1_pre_topc(X2_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X2_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(X1_54) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2044]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7184,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | v2_struct_0(sK2) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_7175,c_2627]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5,plain,
% 7.23/1.49      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.23/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7,plain,
% 7.23/1.49      ( v2_struct_0(X0)
% 7.23/1.49      | ~ l1_struct_0(X0)
% 7.23/1.49      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 7.23/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_370,plain,
% 7.23/1.49      ( v2_struct_0(X0)
% 7.23/1.49      | ~ l1_pre_topc(X0)
% 7.23/1.49      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 7.23/1.49      inference(resolution,[status(thm)],[c_5,c_7]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2029,plain,
% 7.23/1.49      ( v2_struct_0(X0_52)
% 7.23/1.49      | ~ l1_pre_topc(X0_52)
% 7.23/1.49      | ~ v1_xboole_0(u1_struct_0(X0_52)) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_370]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2741,plain,
% 7.23/1.49      ( v2_struct_0(sK2)
% 7.23/1.49      | ~ l1_pre_topc(sK2)
% 7.23/1.49      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2029]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2742,plain,
% 7.23/1.49      ( v2_struct_0(sK2) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.23/1.49      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2741]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_20,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 7.23/1.49      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 7.23/1.49      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 7.23/1.49      | ~ m1_pre_topc(X0,X2)
% 7.23/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.23/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 7.23/1.49      | m1_subset_1(sK0(X1,X2,X0,X3,X4),u1_struct_0(X2))
% 7.23/1.49      | v2_struct_0(X1)
% 7.23/1.49      | v2_struct_0(X2)
% 7.23/1.49      | v2_struct_0(X0)
% 7.23/1.49      | ~ l1_pre_topc(X1)
% 7.23/1.49      | ~ l1_pre_topc(X2)
% 7.23/1.49      | ~ v2_pre_topc(X1)
% 7.23/1.49      | ~ v2_pre_topc(X2)
% 7.23/1.49      | ~ v1_funct_1(X3)
% 7.23/1.49      | ~ v1_funct_1(X4) ),
% 7.23/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2043,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_54,X0_52),X1_54)
% 7.23/1.49      | ~ v1_funct_2(X1_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 7.23/1.49      | ~ v1_funct_2(X0_54,u1_struct_0(X2_52),u1_struct_0(X1_52))
% 7.23/1.49      | ~ m1_pre_topc(X0_52,X2_52)
% 7.23/1.49      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 7.23/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 7.23/1.49      | m1_subset_1(sK0(X1_52,X2_52,X0_52,X0_54,X1_54),u1_struct_0(X2_52))
% 7.23/1.49      | v2_struct_0(X0_52)
% 7.23/1.49      | v2_struct_0(X1_52)
% 7.23/1.49      | v2_struct_0(X2_52)
% 7.23/1.49      | ~ l1_pre_topc(X1_52)
% 7.23/1.49      | ~ l1_pre_topc(X2_52)
% 7.23/1.49      | ~ v2_pre_topc(X1_52)
% 7.23/1.49      | ~ v2_pre_topc(X2_52)
% 7.23/1.49      | ~ v1_funct_1(X0_54)
% 7.23/1.49      | ~ v1_funct_1(X1_54) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_20]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2628,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_54,X0_52),X1_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X1_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
% 7.23/1.49      | m1_subset_1(sK0(X1_52,X2_52,X0_52,X0_54,X1_54),u1_struct_0(X2_52)) = iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X2_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | l1_pre_topc(X2_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X2_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(X1_54) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2043]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7183,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
% 7.23/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | v2_struct_0(sK2) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_7175,c_2628]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7282,plain,
% 7.23/1.49      ( v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_7183,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_2876,
% 7.23/1.49                 c_3151,c_3686]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7283,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(renaming,[status(thm)],[c_7282]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_0,plain,
% 7.23/1.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.23/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2061,plain,
% 7.23/1.49      ( ~ m1_subset_1(X0_54,X0_53)
% 7.23/1.49      | r2_hidden(X0_54,X0_53)
% 7.23/1.49      | v1_xboole_0(X0_53) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_0]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2610,plain,
% 7.23/1.49      ( m1_subset_1(X0_54,X0_53) != iProver_top
% 7.23/1.49      | r2_hidden(X0_54,X0_53) = iProver_top
% 7.23/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2061]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7288,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_7283,c_2610]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7299,plain,
% 7.23/1.49      ( v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_7184,c_36,c_37,c_38,c_2742,c_2876,c_7288]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7300,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(renaming,[status(thm)],[c_7299]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_23,plain,
% 7.23/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.23/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.23/1.49      | ~ r2_hidden(X2,u1_struct_0(X0))
% 7.23/1.49      | v2_struct_0(X1)
% 7.23/1.49      | v2_struct_0(X0)
% 7.23/1.49      | ~ l1_pre_topc(X1)
% 7.23/1.49      | ~ v2_pre_topc(X1)
% 7.23/1.49      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
% 7.23/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2040,plain,
% 7.23/1.49      ( ~ m1_pre_topc(X0_52,X1_52)
% 7.23/1.49      | ~ m1_subset_1(X0_54,u1_struct_0(X1_52))
% 7.23/1.49      | ~ r2_hidden(X0_54,u1_struct_0(X0_52))
% 7.23/1.49      | v2_struct_0(X0_52)
% 7.23/1.49      | v2_struct_0(X1_52)
% 7.23/1.49      | ~ l1_pre_topc(X1_52)
% 7.23/1.49      | ~ v2_pre_topc(X1_52)
% 7.23/1.49      | k1_funct_1(k4_tmap_1(X1_52,X0_52),X0_54) = X0_54 ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_23]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2631,plain,
% 7.23/1.49      ( k1_funct_1(k4_tmap_1(X0_52,X1_52),X0_54) = X0_54
% 7.23/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | r2_hidden(X0_54,u1_struct_0(X1_52)) != iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X0_52) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2040]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7303,plain,
% 7.23/1.49      ( k1_funct_1(k4_tmap_1(X0_52,sK2),sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | v2_struct_0(sK2) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_7300,c_2631]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_8,plain,
% 7.23/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.23/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.23/1.49      | m1_subset_1(X2,u1_struct_0(X1))
% 7.23/1.49      | v2_struct_0(X1)
% 7.23/1.49      | v2_struct_0(X0)
% 7.23/1.49      | ~ l1_pre_topc(X1) ),
% 7.23/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2055,plain,
% 7.23/1.49      ( ~ m1_pre_topc(X0_52,X1_52)
% 7.23/1.49      | ~ m1_subset_1(X0_54,u1_struct_0(X0_52))
% 7.23/1.49      | m1_subset_1(X0_54,u1_struct_0(X1_52))
% 7.23/1.49      | v2_struct_0(X0_52)
% 7.23/1.49      | v2_struct_0(X1_52)
% 7.23/1.49      | ~ l1_pre_topc(X1_52) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2616,plain,
% 7.23/1.49      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,u1_struct_0(X1_52)) = iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X1_52) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2055]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7287,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(X0_52)) = iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | v2_struct_0(sK2) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_7283,c_2616]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_9160,plain,
% 7.23/1.49      ( v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | k1_funct_1(k4_tmap_1(X0_52,sK2),sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_7303,c_37,c_7287]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_9161,plain,
% 7.23/1.49      ( k1_funct_1(k4_tmap_1(X0_52,sK2),sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(renaming,[status(thm)],[c_9160]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_9165,plain,
% 7.23/1.49      ( k1_funct_1(k4_tmap_1(X0_52,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.23/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_2622,c_9161]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_9168,plain,
% 7.23/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.23/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_9165]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7829,plain,
% 7.23/1.49      ( v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(X0_52)) = iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_7287,c_37]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7830,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(X0_52)) = iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(renaming,[status(thm)],[c_7829]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_25,negated_conjecture,
% 7.23/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.23/1.49      | ~ r2_hidden(X0,u1_struct_0(sK2))
% 7.23/1.49      | k1_funct_1(sK3,X0) = X0 ),
% 7.23/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2038,negated_conjecture,
% 7.23/1.49      ( ~ m1_subset_1(X0_54,u1_struct_0(sK1))
% 7.23/1.49      | ~ r2_hidden(X0_54,u1_struct_0(sK2))
% 7.23/1.49      | k1_funct_1(sK3,X0_54) = X0_54 ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_25]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2633,plain,
% 7.23/1.49      ( k1_funct_1(sK3,X0_54) = X0_54
% 7.23/1.49      | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | r2_hidden(X0_54,u1_struct_0(sK2)) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2038]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7833,plain,
% 7.23/1.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_7830,c_2633]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7867,plain,
% 7.23/1.49      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_7833,c_34,c_36,c_37,c_38,c_2742,c_2876,c_7288]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7868,plain,
% 7.23/1.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(renaming,[status(thm)],[c_7867]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7872,plain,
% 7.23/1.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.23/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_2622,c_7868]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_24,negated_conjecture,
% 7.23/1.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
% 7.23/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_45,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2063,plain,( X0_54 = X0_54 ),theory(equality) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2080,plain,
% 7.23/1.49      ( sK3 = sK3 ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2063]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2071,plain,
% 7.23/1.49      ( ~ r2_funct_2(X0_53,X1_53,X0_54,X1_54)
% 7.23/1.49      | r2_funct_2(X0_53,X1_53,X2_54,X3_54)
% 7.23/1.49      | X2_54 != X0_54
% 7.23/1.49      | X3_54 != X1_54 ),
% 7.23/1.49      theory(equality) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2792,plain,
% 7.23/1.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,X1_54)
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
% 7.23/1.49      | k4_tmap_1(sK1,sK2) != X0_54
% 7.23/1.49      | sK3 != X1_54 ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2071]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2793,plain,
% 7.23/1.49      ( k4_tmap_1(sK1,sK2) != X0_54
% 7.23/1.49      | sK3 != X1_54
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,X1_54) != iProver_top
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2792]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2795,plain,
% 7.23/1.49      ( k4_tmap_1(sK1,sK2) != sK3
% 7.23/1.49      | sK3 != sK3
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) != iProver_top ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2793]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_16,plain,
% 7.23/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.23/1.49      | v2_struct_0(X1)
% 7.23/1.49      | ~ l1_pre_topc(X1)
% 7.23/1.49      | ~ v2_pre_topc(X1)
% 7.23/1.49      | v1_funct_1(k4_tmap_1(X1,X0)) ),
% 7.23/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2047,plain,
% 7.23/1.49      ( ~ m1_pre_topc(X0_52,X1_52)
% 7.23/1.49      | v2_struct_0(X1_52)
% 7.23/1.49      | ~ l1_pre_topc(X1_52)
% 7.23/1.49      | ~ v2_pre_topc(X1_52)
% 7.23/1.49      | v1_funct_1(k4_tmap_1(X1_52,X0_52)) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3194,plain,
% 7.23/1.49      ( ~ m1_pre_topc(sK2,sK1)
% 7.23/1.49      | v2_struct_0(sK1)
% 7.23/1.49      | ~ l1_pre_topc(sK1)
% 7.23/1.49      | ~ v2_pre_topc(sK1)
% 7.23/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2047]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3195,plain,
% 7.23/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_3194]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2,plain,
% 7.23/1.49      ( r2_funct_2(X0,X1,X2,X2)
% 7.23/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.23/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.23/1.49      | ~ v1_funct_1(X2) ),
% 7.23/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2059,plain,
% 7.23/1.49      ( r2_funct_2(X0_53,X1_53,X0_54,X0_54)
% 7.23/1.49      | ~ v1_funct_2(X0_54,X0_53,X1_53)
% 7.23/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.23/1.49      | ~ v1_funct_1(X0_54) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2612,plain,
% 7.23/1.49      ( r2_funct_2(X0_53,X1_53,X0_54,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,X0_53,X1_53) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2059]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3604,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) = iProver_top
% 7.23/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_2634,c_2612]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_15,plain,
% 7.23/1.49      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 7.23/1.49      | ~ m1_pre_topc(X1,X0)
% 7.23/1.49      | v2_struct_0(X0)
% 7.23/1.49      | ~ l1_pre_topc(X0)
% 7.23/1.49      | ~ v2_pre_topc(X0) ),
% 7.23/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2048,plain,
% 7.23/1.49      ( v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52))
% 7.23/1.49      | ~ m1_pre_topc(X1_52,X0_52)
% 7.23/1.49      | v2_struct_0(X0_52)
% 7.23/1.49      | ~ l1_pre_topc(X0_52)
% 7.23/1.49      | ~ v2_pre_topc(X0_52) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_15]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4580,plain,
% 7.23/1.49      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.23/1.49      | ~ m1_pre_topc(sK2,sK1)
% 7.23/1.49      | v2_struct_0(sK1)
% 7.23/1.49      | ~ l1_pre_topc(sK1)
% 7.23/1.49      | ~ v2_pre_topc(sK1) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2048]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4581,plain,
% 7.23/1.49      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_4580]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2878,plain,
% 7.23/1.49      ( ~ r2_funct_2(X0_53,X1_53,X0_54,k4_tmap_1(sK1,sK2))
% 7.23/1.49      | ~ v1_funct_2(X0_54,X0_53,X1_53)
% 7.23/1.49      | ~ v1_funct_2(k4_tmap_1(sK1,sK2),X0_53,X1_53)
% 7.23/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.23/1.49      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.23/1.49      | ~ v1_funct_1(X0_54)
% 7.23/1.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.23/1.49      | k4_tmap_1(sK1,sK2) = X0_54 ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2058]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4588,plain,
% 7.23/1.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,k4_tmap_1(sK1,sK2))
% 7.23/1.49      | ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.23/1.49      | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.23/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.23/1.49      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.23/1.49      | ~ v1_funct_1(X0_54)
% 7.23/1.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.23/1.49      | k4_tmap_1(sK1,sK2) = X0_54 ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2878]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4589,plain,
% 7.23/1.49      ( k4_tmap_1(sK1,sK2) = X0_54
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_4588]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4591,plain,
% 7.23/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.23/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_4589]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5039,plain,
% 7.23/1.49      ( ~ m1_pre_topc(sK2,sK1)
% 7.23/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.23/1.49      | v2_struct_0(sK1)
% 7.23/1.49      | ~ l1_pre_topc(sK1)
% 7.23/1.49      | ~ v2_pre_topc(sK1) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_2049]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5040,plain,
% 7.23/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_5039]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7998,plain,
% 7.23/1.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_7872,c_34,c_35,c_36,c_38,c_39,c_40,c_41,c_45,c_2080,
% 7.23/1.49                 c_2795,c_3195,c_3604,c_4581,c_4591,c_5040]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_1,plain,
% 7.23/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.23/1.49      | ~ m1_subset_1(X3,X1)
% 7.23/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.23/1.49      | ~ v1_funct_1(X0)
% 7.23/1.49      | v1_xboole_0(X1)
% 7.23/1.49      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.23/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2060,plain,
% 7.23/1.49      ( ~ v1_funct_2(X0_54,X0_53,X1_53)
% 7.23/1.49      | ~ m1_subset_1(X1_54,X0_53)
% 7.23/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.23/1.49      | ~ v1_funct_1(X0_54)
% 7.23/1.49      | v1_xboole_0(X0_53)
% 7.23/1.49      | k3_funct_2(X0_53,X1_53,X0_54,X1_54) = k1_funct_1(X0_54,X1_54) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2611,plain,
% 7.23/1.49      ( k3_funct_2(X0_53,X1_53,X0_54,X1_54) = k1_funct_1(X0_54,X1_54)
% 7.23/1.49      | v1_funct_2(X0_54,X0_53,X1_53) != iProver_top
% 7.23/1.49      | m1_subset_1(X1_54,X0_53) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2060]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3672,plain,
% 7.23/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = k1_funct_1(sK3,X0_54)
% 7.23/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top
% 7.23/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_2634,c_2611]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3794,plain,
% 7.23/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = k1_funct_1(sK3,X0_54)
% 7.23/1.49      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_3672,c_36,c_37,c_38,c_39,c_40,c_2742,c_2876]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5297,plain,
% 7.23/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_54,X1_54)) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_54,X1_54))
% 7.23/1.49      | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),k2_tmap_1(sK2,X0_52,X0_54,X1_52),X1_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X1_54,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X1_52,sK2) != iProver_top
% 7.23/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | v2_struct_0(sK2) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.23/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(X1_54) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_2628,c_3794]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_6504,plain,
% 7.23/1.49      ( v2_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | m1_pre_topc(X1_52,sK2) != iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | v1_funct_2(X1_54,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),k2_tmap_1(sK2,X0_52,X0_54,X1_52),X1_54) = iProver_top
% 7.23/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_54,X1_54)) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_54,X1_54))
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(X1_54) != iProver_top ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_5297,c_35,c_36,c_37,c_38,c_2876,c_3151]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_6505,plain,
% 7.23/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_54,X1_54)) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_54,X1_54))
% 7.23/1.49      | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),k2_tmap_1(sK2,X0_52,X0_54,X1_52),X1_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X1_54,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X1_52,sK2) != iProver_top
% 7.23/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(X1_54) != iProver_top ),
% 7.23/1.49      inference(renaming,[status(thm)],[c_6504]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3921,plain,
% 7.23/1.49      ( k4_tmap_1(X0_52,X1_52) = X0_54
% 7.23/1.49      | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_54,k4_tmap_1(X0_52,X1_52)) != iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_2622,c_2613]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2110,plain,
% 7.23/1.49      ( v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) = iProver_top
% 7.23/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X0_52) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2048]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7029,plain,
% 7.23/1.49      ( v1_funct_2(X0_54,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_54,k4_tmap_1(X0_52,X1_52)) != iProver_top
% 7.23/1.49      | k4_tmap_1(X0_52,X1_52) = X0_54
% 7.23/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_3921,c_2110]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7030,plain,
% 7.23/1.49      ( k4_tmap_1(X0_52,X1_52) = X0_54
% 7.23/1.49      | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_54,k4_tmap_1(X0_52,X1_52)) != iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
% 7.23/1.49      inference(renaming,[status(thm)],[c_7029]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7039,plain,
% 7.23/1.49      ( k2_tmap_1(sK2,X0_52,X0_54,X1_52) = k4_tmap_1(X0_52,X1_52)
% 7.23/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_54,k4_tmap_1(X0_52,X1_52))) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_54,k4_tmap_1(X0_52,X1_52)))
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | v1_funct_2(k2_tmap_1(sK2,X0_52,X0_54,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.23/1.49      | m1_pre_topc(X1_52,sK2) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | m1_subset_1(k2_tmap_1(sK2,X0_52,X0_54,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(k2_tmap_1(sK2,X0_52,X0_54,X1_52)) != iProver_top
% 7.23/1.49      | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_6505,c_7030]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7306,plain,
% 7.23/1.49      ( v1_funct_2(k2_tmap_1(sK2,X0_52,X0_54,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_54,k4_tmap_1(X0_52,X1_52))) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_54,k4_tmap_1(X0_52,X1_52)))
% 7.23/1.49      | k2_tmap_1(sK2,X0_52,X0_54,X1_52) = k4_tmap_1(X0_52,X1_52)
% 7.23/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.23/1.49      | m1_pre_topc(X1_52,sK2) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | m1_subset_1(k2_tmap_1(sK2,X0_52,X0_54,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(k2_tmap_1(sK2,X0_52,X0_54,X1_52)) != iProver_top
% 7.23/1.49      | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_7039,c_2110]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7307,plain,
% 7.23/1.49      ( k2_tmap_1(sK2,X0_52,X0_54,X1_52) = k4_tmap_1(X0_52,X1_52)
% 7.23/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_54,k4_tmap_1(X0_52,X1_52))) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_54,k4_tmap_1(X0_52,X1_52)))
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | v1_funct_2(k2_tmap_1(sK2,X0_52,X0_54,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.23/1.49      | m1_pre_topc(X1_52,sK2) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | m1_subset_1(k2_tmap_1(sK2,X0_52,X0_54,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(k2_tmap_1(sK2,X0_52,X0_54,X1_52)) != iProver_top
% 7.23/1.49      | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
% 7.23/1.49      inference(renaming,[status(thm)],[c_7306]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7312,plain,
% 7.23/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = k4_tmap_1(sK1,sK2)
% 7.23/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 7.23/1.49      | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.23/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | v2_struct_0(sK2) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 7.23/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_7175,c_7307]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7313,plain,
% 7.23/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 7.23/1.49      | k4_tmap_1(sK1,sK2) = sK3
% 7.23/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.23/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | v2_struct_0(sK2) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(light_normalisation,[status(thm)],[c_7312,c_7175]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7185,plain,
% 7.23/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54))
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | v2_struct_0(sK2) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_7175,c_6505]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7270,plain,
% 7.23/1.49      ( v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54))
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_7185,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_2876,
% 7.23/1.49                 c_3686]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7271,plain,
% 7.23/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54))
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top ),
% 7.23/1.49      inference(renaming,[status(thm)],[c_7270]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7275,plain,
% 7.23/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.23/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_2622,c_7271]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7316,plain,
% 7.23/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_7313,c_34,c_35,c_36,c_38,c_39,c_40,c_41,c_45,c_2080,
% 7.23/1.49                 c_2795,c_3195,c_3604,c_4581,c_4591,c_5040,c_7275]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_18,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 7.23/1.49      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 7.23/1.49      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 7.23/1.49      | ~ m1_pre_topc(X0,X2)
% 7.23/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.23/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 7.23/1.49      | v2_struct_0(X1)
% 7.23/1.49      | v2_struct_0(X2)
% 7.23/1.49      | v2_struct_0(X0)
% 7.23/1.49      | ~ l1_pre_topc(X1)
% 7.23/1.49      | ~ l1_pre_topc(X2)
% 7.23/1.49      | ~ v2_pre_topc(X1)
% 7.23/1.49      | ~ v2_pre_topc(X2)
% 7.23/1.49      | ~ v1_funct_1(X3)
% 7.23/1.49      | ~ v1_funct_1(X4)
% 7.23/1.49      | k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,sK0(X1,X2,X0,X3,X4)) != k1_funct_1(X4,sK0(X1,X2,X0,X3,X4)) ),
% 7.23/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2045,plain,
% 7.23/1.49      ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_54,X0_52),X1_54)
% 7.23/1.49      | ~ v1_funct_2(X1_54,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 7.23/1.49      | ~ v1_funct_2(X0_54,u1_struct_0(X2_52),u1_struct_0(X1_52))
% 7.23/1.49      | ~ m1_pre_topc(X0_52,X2_52)
% 7.23/1.49      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 7.23/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 7.23/1.49      | v2_struct_0(X0_52)
% 7.23/1.49      | v2_struct_0(X1_52)
% 7.23/1.49      | v2_struct_0(X2_52)
% 7.23/1.49      | ~ l1_pre_topc(X1_52)
% 7.23/1.49      | ~ l1_pre_topc(X2_52)
% 7.23/1.49      | ~ v2_pre_topc(X1_52)
% 7.23/1.49      | ~ v2_pre_topc(X2_52)
% 7.23/1.49      | ~ v1_funct_1(X0_54)
% 7.23/1.49      | ~ v1_funct_1(X1_54)
% 7.23/1.49      | k3_funct_2(u1_struct_0(X2_52),u1_struct_0(X1_52),X0_54,sK0(X1_52,X2_52,X0_52,X0_54,X1_54)) != k1_funct_1(X1_54,sK0(X1_52,X2_52,X0_52,X0_54,X1_54)) ),
% 7.23/1.49      inference(subtyping,[status(esa)],[c_18]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2626,plain,
% 7.23/1.49      ( k3_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_54,sK0(X1_52,X0_52,X2_52,X0_54,X1_54)) != k1_funct_1(X1_54,sK0(X1_52,X0_52,X2_52,X0_54,X1_54))
% 7.23/1.49      | r2_funct_2(u1_struct_0(X2_52),u1_struct_0(X1_52),k2_tmap_1(X0_52,X1_52,X0_54,X2_52),X1_54) = iProver_top
% 7.23/1.49      | v1_funct_2(X1_54,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
% 7.23/1.49      | v1_funct_2(X0_54,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 7.23/1.49      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 7.23/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
% 7.23/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 7.23/1.49      | v2_struct_0(X2_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.23/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.23/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X1_52) != iProver_top
% 7.23/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.23/1.49      | v1_funct_1(X0_54) != iProver_top
% 7.23/1.49      | v1_funct_1(X1_54) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_2045]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7318,plain,
% 7.23/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),k4_tmap_1(sK1,sK2)) = iProver_top
% 7.23/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.23/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | v2_struct_0(sK2) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.23/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_7316,c_2626]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7319,plain,
% 7.23/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 7.23/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.23/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.23/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.23/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.23/1.49      | v2_struct_0(sK1) = iProver_top
% 7.23/1.49      | v2_struct_0(sK2) = iProver_top
% 7.23/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.23/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.23/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.23/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.23/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.23/1.49      inference(light_normalisation,[status(thm)],[c_7318,c_7175]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7322,plain,
% 7.23/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
% 7.23/1.49      inference(global_propositional_subsumption,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_7319,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_45,
% 7.23/1.49                 c_2080,c_2795,c_2876,c_3151,c_3195,c_3604,c_3686,c_4581,
% 7.23/1.49                 c_4591,c_5040]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_8000,plain,
% 7.23/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 7.23/1.49      inference(demodulation,[status(thm)],[c_7998,c_7322]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(contradiction,plain,
% 7.23/1.49      ( $false ),
% 7.23/1.49      inference(minisat,
% 7.23/1.49                [status(thm)],
% 7.23/1.49                [c_9168,c_8000,c_5040,c_4591,c_4581,c_3604,c_3195,c_2795,
% 7.23/1.49                 c_2080,c_45,c_41,c_40,c_39,c_38,c_36,c_35,c_34]) ).
% 7.23/1.49  
% 7.23/1.49  
% 7.23/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.23/1.49  
% 7.23/1.49  ------                               Statistics
% 7.23/1.49  
% 7.23/1.49  ------ General
% 7.23/1.49  
% 7.23/1.49  abstr_ref_over_cycles:                  0
% 7.23/1.49  abstr_ref_under_cycles:                 0
% 7.23/1.49  gc_basic_clause_elim:                   0
% 7.23/1.49  forced_gc_time:                         0
% 7.23/1.49  parsing_time:                           0.016
% 7.23/1.49  unif_index_cands_time:                  0.
% 7.23/1.49  unif_index_add_time:                    0.
% 7.23/1.49  orderings_time:                         0.
% 7.23/1.49  out_proof_time:                         0.023
% 7.23/1.49  total_time:                             0.588
% 7.23/1.49  num_of_symbols:                         59
% 7.23/1.49  num_of_terms:                           16572
% 7.23/1.49  
% 7.23/1.49  ------ Preprocessing
% 7.23/1.49  
% 7.23/1.49  num_of_splits:                          0
% 7.23/1.49  num_of_split_atoms:                     0
% 7.23/1.49  num_of_reused_defs:                     0
% 7.23/1.49  num_eq_ax_congr_red:                    72
% 7.23/1.49  num_of_sem_filtered_clauses:            1
% 7.23/1.49  num_of_subtypes:                        4
% 7.23/1.49  monotx_restored_types:                  1
% 7.23/1.49  sat_num_of_epr_types:                   0
% 7.23/1.49  sat_num_of_non_cyclic_types:            0
% 7.23/1.49  sat_guarded_non_collapsed_types:        1
% 7.23/1.49  num_pure_diseq_elim:                    0
% 7.23/1.49  simp_replaced_by:                       0
% 7.23/1.49  res_preprocessed:                       152
% 7.23/1.49  prep_upred:                             0
% 7.23/1.49  prep_unflattend:                        70
% 7.23/1.49  smt_new_axioms:                         0
% 7.23/1.49  pred_elim_cands:                        10
% 7.23/1.49  pred_elim:                              1
% 7.23/1.49  pred_elim_cl:                           1
% 7.23/1.49  pred_elim_cycles:                       7
% 7.23/1.49  merged_defs:                            0
% 7.23/1.49  merged_defs_ncl:                        0
% 7.23/1.49  bin_hyper_res:                          0
% 7.23/1.49  prep_cycles:                            4
% 7.23/1.49  pred_elim_time:                         0.046
% 7.23/1.49  splitting_time:                         0.
% 7.23/1.49  sem_filter_time:                        0.
% 7.23/1.49  monotx_time:                            0.001
% 7.23/1.49  subtype_inf_time:                       0.002
% 7.23/1.49  
% 7.23/1.49  ------ Problem properties
% 7.23/1.49  
% 7.23/1.49  clauses:                                33
% 7.23/1.49  conjectures:                            10
% 7.23/1.49  epr:                                    11
% 7.23/1.49  horn:                                   17
% 7.23/1.49  ground:                                 9
% 7.23/1.49  unary:                                  9
% 7.23/1.49  binary:                                 1
% 7.23/1.49  lits:                                   199
% 7.23/1.49  lits_eq:                                7
% 7.23/1.49  fd_pure:                                0
% 7.23/1.49  fd_pseudo:                              0
% 7.23/1.49  fd_cond:                                0
% 7.23/1.49  fd_pseudo_cond:                         1
% 7.23/1.49  ac_symbols:                             0
% 7.23/1.49  
% 7.23/1.49  ------ Propositional Solver
% 7.23/1.49  
% 7.23/1.49  prop_solver_calls:                      29
% 7.23/1.49  prop_fast_solver_calls:                 3467
% 7.23/1.49  smt_solver_calls:                       0
% 7.23/1.49  smt_fast_solver_calls:                  0
% 7.23/1.49  prop_num_of_clauses:                    3604
% 7.23/1.49  prop_preprocess_simplified:             11465
% 7.23/1.49  prop_fo_subsumed:                       254
% 7.23/1.49  prop_solver_time:                       0.
% 7.23/1.49  smt_solver_time:                        0.
% 7.23/1.49  smt_fast_solver_time:                   0.
% 7.23/1.49  prop_fast_solver_time:                  0.
% 7.23/1.49  prop_unsat_core_time:                   0.
% 7.23/1.49  
% 7.23/1.49  ------ QBF
% 7.23/1.49  
% 7.23/1.49  qbf_q_res:                              0
% 7.23/1.49  qbf_num_tautologies:                    0
% 7.23/1.49  qbf_prep_cycles:                        0
% 7.23/1.49  
% 7.23/1.49  ------ BMC1
% 7.23/1.49  
% 7.23/1.49  bmc1_current_bound:                     -1
% 7.23/1.49  bmc1_last_solved_bound:                 -1
% 7.23/1.49  bmc1_unsat_core_size:                   -1
% 7.23/1.49  bmc1_unsat_core_parents_size:           -1
% 7.23/1.49  bmc1_merge_next_fun:                    0
% 7.23/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.23/1.49  
% 7.23/1.49  ------ Instantiation
% 7.23/1.49  
% 7.23/1.49  inst_num_of_clauses:                    946
% 7.23/1.49  inst_num_in_passive:                    346
% 7.23/1.49  inst_num_in_active:                     447
% 7.23/1.49  inst_num_in_unprocessed:                153
% 7.23/1.49  inst_num_of_loops:                      520
% 7.23/1.49  inst_num_of_learning_restarts:          0
% 7.23/1.49  inst_num_moves_active_passive:          71
% 7.23/1.49  inst_lit_activity:                      0
% 7.23/1.49  inst_lit_activity_moves:                1
% 7.23/1.49  inst_num_tautologies:                   0
% 7.23/1.49  inst_num_prop_implied:                  0
% 7.23/1.49  inst_num_existing_simplified:           0
% 7.23/1.49  inst_num_eq_res_simplified:             0
% 7.23/1.49  inst_num_child_elim:                    0
% 7.23/1.49  inst_num_of_dismatching_blockings:      456
% 7.23/1.49  inst_num_of_non_proper_insts:           768
% 7.23/1.49  inst_num_of_duplicates:                 0
% 7.23/1.49  inst_inst_num_from_inst_to_res:         0
% 7.23/1.49  inst_dismatching_checking_time:         0.
% 7.23/1.49  
% 7.23/1.49  ------ Resolution
% 7.23/1.49  
% 7.23/1.49  res_num_of_clauses:                     0
% 7.23/1.49  res_num_in_passive:                     0
% 7.23/1.49  res_num_in_active:                      0
% 7.23/1.49  res_num_of_loops:                       156
% 7.23/1.49  res_forward_subset_subsumed:            9
% 7.23/1.49  res_backward_subset_subsumed:           0
% 7.23/1.49  res_forward_subsumed:                   0
% 7.23/1.49  res_backward_subsumed:                  0
% 7.23/1.49  res_forward_subsumption_resolution:     0
% 7.23/1.49  res_backward_subsumption_resolution:    0
% 7.23/1.49  res_clause_to_clause_subsumption:       754
% 7.23/1.49  res_orphan_elimination:                 0
% 7.23/1.49  res_tautology_del:                      36
% 7.23/1.49  res_num_eq_res_simplified:              0
% 7.23/1.49  res_num_sel_changes:                    0
% 7.23/1.49  res_moves_from_active_to_pass:          0
% 7.23/1.49  
% 7.23/1.49  ------ Superposition
% 7.23/1.49  
% 7.23/1.49  sup_time_total:                         0.
% 7.23/1.49  sup_time_generating:                    0.
% 7.23/1.49  sup_time_sim_full:                      0.
% 7.23/1.49  sup_time_sim_immed:                     0.
% 7.23/1.49  
% 7.23/1.49  sup_num_of_clauses:                     122
% 7.23/1.49  sup_num_in_active:                      92
% 7.23/1.49  sup_num_in_passive:                     30
% 7.23/1.49  sup_num_of_loops:                       102
% 7.23/1.49  sup_fw_superposition:                   80
% 7.23/1.49  sup_bw_superposition:                   70
% 7.23/1.49  sup_immediate_simplified:               35
% 7.23/1.49  sup_given_eliminated:                   1
% 7.23/1.49  comparisons_done:                       0
% 7.23/1.49  comparisons_avoided:                    6
% 7.23/1.49  
% 7.23/1.49  ------ Simplifications
% 7.23/1.49  
% 7.23/1.49  
% 7.23/1.49  sim_fw_subset_subsumed:                 18
% 7.23/1.49  sim_bw_subset_subsumed:                 5
% 7.23/1.49  sim_fw_subsumed:                        13
% 7.23/1.49  sim_bw_subsumed:                        3
% 7.23/1.49  sim_fw_subsumption_res:                 0
% 7.23/1.49  sim_bw_subsumption_res:                 0
% 7.23/1.49  sim_tautology_del:                      7
% 7.23/1.49  sim_eq_tautology_del:                   2
% 7.23/1.49  sim_eq_res_simp:                        0
% 7.23/1.49  sim_fw_demodulated:                     5
% 7.23/1.49  sim_bw_demodulated:                     8
% 7.23/1.49  sim_light_normalised:                   19
% 7.23/1.49  sim_joinable_taut:                      0
% 7.23/1.49  sim_joinable_simp:                      0
% 7.23/1.49  sim_ac_normalised:                      0
% 7.23/1.49  sim_smt_subsumption:                    0
% 7.23/1.49  
%------------------------------------------------------------------------------
