%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:44 EST 2020

% Result     : Theorem 39.25s
% Output     : CNFRefutation 39.25s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2542)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f50,plain,(
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
    inference(flattening,[],[f50])).

fof(f61,plain,(
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
     => ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK4)
        & ! [X3] :
            ( k1_funct_1(sK4,X3) = X3
            | ~ r2_hidden(X3,u1_struct_0(X1))
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
            ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k4_tmap_1(X0,sK3),X2)
            & ! [X3] :
                ( k1_funct_1(X2,X3) = X3
                | ~ r2_hidden(X3,u1_struct_0(sK3))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
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
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK2),k4_tmap_1(sK2,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4)
    & ! [X3] :
        ( k1_funct_1(sK4,X3) = X3
        | ~ r2_hidden(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f51,f61,f60,f59])).

fof(f96,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f62])).

fof(f3,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
        & m1_subset_1(sK0(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f53,f54])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | m1_subset_1(sK0(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f94,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f95,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f62])).

fof(f89,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f90,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f91,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f93,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
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
    inference(flattening,[],[f48])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f98,plain,(
    ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f82,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f69])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f35])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f37])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
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
    inference(flattening,[],[f44])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f37])).

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
                             => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k1_funct_1(X4,X5) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
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

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k1_funct_1(X4,X5) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
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
    inference(flattening,[],[f42])).

fof(f57,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X4,X5) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( k1_funct_1(X4,sK1(X0,X1,X2,X3,X4)) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK1(X0,X1,X2,X3,X4))
        & r2_hidden(sK1(X0,X1,X2,X3,X4),u1_struct_0(X2))
        & m1_subset_1(sK1(X0,X1,X2,X3,X4),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ( k1_funct_1(X4,sK1(X0,X1,X2,X3,X4)) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK1(X0,X1,X2,X3,X4))
                        & r2_hidden(sK1(X0,X1,X2,X3,X4),u1_struct_0(X2))
                        & m1_subset_1(sK1(X0,X1,X2,X3,X4),u1_struct_0(X1)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f57])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | r2_hidden(sK1(X0,X1,X2,X3,X4),u1_struct_0(X2))
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
    inference(cnf_transformation,[],[f58])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f97,plain,(
    ! [X3] :
      ( k1_funct_1(sK4,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1635,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | m1_subset_1(k4_tmap_1(X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2265,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_subset_1(k4_tmap_1(X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1635])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1622,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_2278,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1622])).

cnf(c_3,plain,
    ( r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK0(X0,X2,X3),X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1647,plain,
    ( r2_funct_2(X0_53,X1_53,X2_53,X3_53)
    | ~ v1_funct_2(X3_53,X0_53,X1_53)
    | ~ v1_funct_2(X2_53,X0_53,X1_53)
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | m1_subset_1(sK0(X0_53,X2_53,X3_53),X0_53)
    | ~ v1_funct_1(X2_53)
    | ~ v1_funct_1(X3_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2253,plain,
    ( r2_funct_2(X0_53,X1_53,X2_53,X3_53) = iProver_top
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X3_53,X0_53,X1_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(sK0(X0_53,X2_53,X3_53),X0_53) = iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1647])).

cnf(c_3875,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4,X0_53),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2278,c_2253])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_41,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_42,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4035,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4,X0_53),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3875,c_41,c_42])).

cnf(c_4036,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4,X0_53),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_4035])).

cnf(c_4040,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2265,c_4036])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_36,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_37,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_38,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_40,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1633,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52)
    | v1_funct_1(k4_tmap_1(X1_52,X0_52)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2596,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v1_funct_1(k4_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1633])).

cnf(c_2597,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2596])).

cnf(c_16,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1634,plain,
    ( v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52))
    | ~ m1_pre_topc(X1_52,X0_52)
    | v2_struct_0(X0_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2757,plain,
    ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1634])).

cnf(c_2758,plain,
    ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2757])).

cnf(c_4120,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4040,c_36,c_37,c_38,c_40,c_2597,c_2758])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1650,plain,
    ( ~ m1_subset_1(X0_53,X1_53)
    | r2_hidden(X0_53,X1_53)
    | v1_xboole_0(X1_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2250,plain,
    ( m1_subset_1(X0_53,X1_53) != iProver_top
    | r2_hidden(X0_53,X1_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1650])).

cnf(c_4126,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4120,c_2250])).

cnf(c_1619,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_2281,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1619])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1641,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | m1_subset_1(X0_53,u1_struct_0(X1_52))
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | ~ l1_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2259,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1641])).

cnf(c_4125,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | m1_pre_topc(sK3,X0_52) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X0_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_4120,c_2259])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_39,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4280,plain,
    ( v2_struct_0(X0_52) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X0_52)) = iProver_top
    | m1_pre_topc(sK3,X0_52) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4125,c_39])).

cnf(c_4281,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | m1_pre_topc(sK3,X0_52) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X0_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_4280])).

cnf(c_4288,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(sK3,X0_52) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X1_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_4281,c_2259])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1642,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ l1_pre_topc(X1_52)
    | l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1696,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1642])).

cnf(c_7648,plain,
    ( v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X1_52)) = iProver_top
    | m1_pre_topc(sK3,X0_52) != iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4288,c_1696])).

cnf(c_7649,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(sK3,X0_52) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X1_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_7648])).

cnf(c_7652,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2281,c_7649])).

cnf(c_4283,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4281])).

cnf(c_7656,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7652,c_36,c_38,c_40,c_4283])).

cnf(c_7657,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7656])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1625,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X1_52))
    | ~ r2_hidden(X0_53,u1_struct_0(X0_52))
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52)
    | k1_funct_1(k4_tmap_1(X1_52,X0_52),X0_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2275,plain,
    ( k1_funct_1(k4_tmap_1(X0_52,X1_52),X0_53) = X0_53
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | r2_hidden(X0_53,u1_struct_0(X1_52)) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1625])).

cnf(c_7661,plain,
    ( k1_funct_1(k4_tmap_1(sK2,X0_52),sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | m1_pre_topc(X0_52,sK2) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7657,c_2275])).

cnf(c_7857,plain,
    ( v2_struct_0(X0_52) = iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X0_52,sK2) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | k1_funct_1(k4_tmap_1(sK2,X0_52),sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7661,c_36,c_37,c_38])).

cnf(c_7858,plain,
    ( k1_funct_1(k4_tmap_1(sK2,X0_52),sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | m1_pre_topc(X0_52,sK2) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top ),
    inference(renaming,[status(thm)],[c_7857])).

cnf(c_7864,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4126,c_7858])).

cnf(c_8118,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7864,c_39,c_40])).

cnf(c_6,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1644,plain,
    ( ~ r2_funct_2(X0_53,X1_53,X2_53,X3_53)
    | ~ v1_funct_2(X3_53,X0_53,X1_53)
    | ~ v1_funct_2(X2_53,X0_53,X1_53)
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X2_53)
    | ~ v1_funct_1(X3_53)
    | X3_53 = X2_53 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2256,plain,
    ( X0_53 = X1_53
    | r2_funct_2(X2_53,X3_53,X1_53,X0_53) != iProver_top
    | v1_funct_2(X1_53,X2_53,X3_53) != iProver_top
    | v1_funct_2(X0_53,X2_53,X3_53) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1644])).

cnf(c_3882,plain,
    ( k4_tmap_1(X0_52,X1_52) = X0_53
    | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_53,k4_tmap_1(X0_52,X1_52)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2265,c_2256])).

cnf(c_1714,plain,
    ( v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) = iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1634])).

cnf(c_7488,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_53,k4_tmap_1(X0_52,X1_52)) != iProver_top
    | k4_tmap_1(X0_52,X1_52) = X0_53
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3882,c_1714])).

cnf(c_7489,plain,
    ( k4_tmap_1(X0_52,X1_52) = X0_53
    | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_53,k4_tmap_1(X0_52,X1_52)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7488])).

cnf(c_8122,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8118,c_7489])).

cnf(c_26,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_47,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1652,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_1675,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_2468,plain,
    ( ~ m1_pre_topc(sK3,X0_52)
    | ~ l1_pre_topc(X0_52)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_2470,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2468])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1643,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52)
    | v2_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2791,plain,
    ( ~ m1_pre_topc(sK3,X0_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X0_52)
    | v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1643])).

cnf(c_2793,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2791])).

cnf(c_19,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1631,plain,
    ( m1_pre_topc(X0_52,X0_52)
    | ~ l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3078,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1631])).

cnf(c_3139,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1635])).

cnf(c_3238,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_5,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1645,plain,
    ( r2_funct_2(X0_53,X1_53,X2_53,X2_53)
    | ~ v1_funct_2(X2_53,X0_53,X1_53)
    | ~ m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X2_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2255,plain,
    ( r2_funct_2(X0_53,X1_53,X2_53,X2_53) = iProver_top
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1645])).

cnf(c_3279,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,sK4) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2278,c_2255])).

cnf(c_1657,plain,
    ( ~ r2_funct_2(X0_53,X1_53,X2_53,X3_53)
    | r2_funct_2(X4_53,X5_53,X6_53,X7_53)
    | X4_53 != X0_53
    | X5_53 != X1_53
    | X6_53 != X2_53
    | X7_53 != X3_53 ),
    theory(equality)).

cnf(c_2453,plain,
    ( ~ r2_funct_2(X0_53,X1_53,X2_53,X3_53)
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4)
    | k4_tmap_1(sK2,sK3) != X2_53
    | u1_struct_0(sK2) != X1_53
    | u1_struct_0(sK3) != X0_53
    | sK4 != X3_53 ),
    inference(instantiation,[status(thm)],[c_1657])).

cnf(c_2646,plain,
    ( ~ r2_funct_2(X0_53,u1_struct_0(sK2),X1_53,X2_53)
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4)
    | k4_tmap_1(sK2,sK3) != X1_53
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != X0_53
    | sK4 != X2_53 ),
    inference(instantiation,[status(thm)],[c_2453])).

cnf(c_5050,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),X0_53,X1_53)
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4)
    | k4_tmap_1(sK2,sK3) != X0_53
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != X1_53 ),
    inference(instantiation,[status(thm)],[c_2646])).

cnf(c_5051,plain,
    ( k4_tmap_1(sK2,sK3) != X0_53
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != X1_53
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),X0_53,X1_53) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5050])).

cnf(c_5053,plain,
    ( k4_tmap_1(sK2,sK3) != sK4
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK4 != sK4
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5051])).

cnf(c_6383,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_8120,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8118])).

cnf(c_5080,plain,
    ( ~ r2_funct_2(X0_53,X1_53,X2_53,k4_tmap_1(X0_52,X1_52))
    | ~ v1_funct_2(X2_53,X0_53,X1_53)
    | ~ v1_funct_2(k4_tmap_1(X0_52,X1_52),X0_53,X1_53)
    | ~ m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X2_53)
    | ~ v1_funct_1(k4_tmap_1(X0_52,X1_52))
    | k4_tmap_1(X0_52,X1_52) = X2_53 ),
    inference(instantiation,[status(thm)],[c_1644])).

cnf(c_8260,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(X0_52,X1_52))
    | ~ v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k4_tmap_1(X0_52,X1_52))
    | ~ v1_funct_1(sK4)
    | k4_tmap_1(X0_52,X1_52) = sK4 ),
    inference(instantiation,[status(thm)],[c_5080])).

cnf(c_8334,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3))
    | ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
    | ~ v1_funct_1(sK4)
    | k4_tmap_1(sK2,sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_8260])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1632,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | m1_subset_1(u1_struct_0(X0_52),k1_zfmisc_1(u1_struct_0(X1_52)))
    | ~ l1_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_26945,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1632])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f74])).

cnf(c_1639,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X2_52,X0_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | ~ m1_pre_topc(X2_52,X3_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | v2_struct_0(X1_52)
    | v2_struct_0(X3_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X3_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X3_52)
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2261,plain,
    ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53)
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_pre_topc(X0_52,X3_52) != iProver_top
    | m1_pre_topc(X2_52,X3_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X3_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X3_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X3_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1639])).

cnf(c_4529,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK2,sK3,X0_52,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2278,c_2261])).

cnf(c_4879,plain,
    ( l1_pre_topc(X1_52) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK2,sK3,X0_52,sK4)
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4529,c_36,c_37,c_38,c_41,c_42,c_43,c_2542])).

cnf(c_4880,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK2,sK3,X0_52,sK4)
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_4879])).

cnf(c_4885,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK2,sK2,sK3,sK3,sK4)
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2281,c_4880])).

cnf(c_2269,plain,
    ( m1_pre_topc(X0_52,X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1631])).

cnf(c_10,plain,
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
    inference(cnf_transformation,[],[f73])).

cnf(c_1640,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X2_52,X0_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X0_52)
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_53,X2_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2260,plain,
    ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_53,X2_52)
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1640])).

cnf(c_4026,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK3,sK2,sK4,X0_52)
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0_52,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2278,c_2260])).

cnf(c_2469,plain,
    ( m1_pre_topc(sK3,X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2468])).

cnf(c_2471,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2469])).

cnf(c_2792,plain,
    ( m1_pre_topc(sK3,X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2791])).

cnf(c_2794,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2792])).

cnf(c_4092,plain,
    ( m1_pre_topc(X0_52,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK3,sK2,sK4,X0_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4026,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_2471,c_2794])).

cnf(c_4093,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK3,sK2,sK4,X0_52)
    | m1_pre_topc(X0_52,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4092])).

cnf(c_4098,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK3,sK2,sK4,sK3)
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2269,c_4093])).

cnf(c_4101,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK3,sK2,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4098,c_38,c_40,c_2471])).

cnf(c_4887,plain,
    ( k3_tmap_1(sK2,sK2,sK3,sK3,sK4) = k2_tmap_1(sK3,sK2,sK4,sK3)
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4885,c_4101])).

cnf(c_3079,plain,
    ( m1_pre_topc(sK3,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3078])).

cnf(c_4921,plain,
    ( k3_tmap_1(sK2,sK2,sK3,sK3,sK4) = k2_tmap_1(sK3,sK2,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4887,c_36,c_37,c_38,c_40,c_2471,c_3079])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f77])).

cnf(c_1638,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_pre_topc(X3_52,X2_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | m1_subset_1(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2262,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_pre_topc(X3_52,X2_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52)))) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1638])).

cnf(c_4924,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4921,c_2262])).

cnf(c_43,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5425,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4924,c_36,c_37,c_38,c_40,c_41,c_42,c_43])).

cnf(c_3732,plain,
    ( sK4 = X0_53
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),X0_53,sK4) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2278,c_2256])).

cnf(c_3735,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | sK4 = X0_53
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),X0_53,sK4) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3732,c_41,c_42])).

cnf(c_3736,plain,
    ( sK4 = X0_53
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),X0_53,sK4) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_3735])).

cnf(c_5440,plain,
    ( k2_tmap_1(sK3,sK2,sK4,sK3) = sK4
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK3,sK2,sK4,sK3),sK4) != iProver_top
    | v1_funct_2(k2_tmap_1(sK3,sK2,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK2,sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5425,c_3736])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f86])).

cnf(c_1627,plain,
    ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,k3_tmap_1(X2_52,X1_52,X0_52,X0_52,X0_53))
    | ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2273,plain,
    ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,k3_tmap_1(X2_52,X1_52,X0_52,X0_52,X0_53)) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1627])).

cnf(c_4923,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k2_tmap_1(sK3,sK2,sK4,sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4921,c_2273])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f76])).

cnf(c_1637,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | v1_funct_2(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53),u1_struct_0(X3_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_pre_topc(X3_52,X2_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2263,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53),u1_struct_0(X3_52),u1_struct_0(X1_52)) = iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_pre_topc(X3_52,X2_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1637])).

cnf(c_4925,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK2,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4921,c_2263])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f75])).

cnf(c_1636,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_pre_topc(X3_52,X2_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2264,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_pre_topc(X3_52,X2_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1636])).

cnf(c_4722,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(sK3,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_52,sK2,sK3,X0_52,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2278,c_2264])).

cnf(c_4872,plain,
    ( v1_funct_1(k3_tmap_1(X1_52,sK2,sK3,X0_52,sK4)) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(sK3,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4722,c_36,c_37,c_38,c_41,c_42])).

cnf(c_4873,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(sK3,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_52,sK2,sK3,X0_52,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4872])).

cnf(c_4926,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK2,sK4,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4921,c_4873])).

cnf(c_5436,plain,
    ( k2_tmap_1(sK3,sK2,sK4,sK3) = X0_53
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),X0_53,k2_tmap_1(sK3,sK2,sK4,sK3)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK3,sK2,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK2,sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5425,c_2256])).

cnf(c_5459,plain,
    ( k2_tmap_1(sK3,sK2,sK4,sK3) = sK4
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k2_tmap_1(sK3,sK2,sK4,sK3)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK3,sK2,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK2,sK4,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5436])).

cnf(c_5470,plain,
    ( k2_tmap_1(sK3,sK2,sK4,sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5440,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_4923,c_4925,c_4926,c_5459])).

cnf(c_21,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | r2_hidden(sK1(X1,X2,X0,X3,X4),u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1629,plain,
    ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_53,X0_52),X1_53)
    | ~ v1_funct_2(X1_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ v1_funct_2(X0_53,u1_struct_0(X2_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | r2_hidden(sK1(X1_52,X2_52,X0_52,X0_53,X1_53),u1_struct_0(X0_52))
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2271,plain,
    ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_53,X0_52),X1_53) = iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
    | r2_hidden(sK1(X1_52,X2_52,X0_52,X0_53,X1_53),u1_struct_0(X0_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1629])).

cnf(c_7495,plain,
    ( k2_tmap_1(X0_52,X1_52,X0_53,X2_52) = k4_tmap_1(X1_52,X2_52)
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_52,X1_52,X0_53,X2_52),u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
    | v1_funct_2(k4_tmap_1(X1_52,X2_52),u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X2_52,X1_52) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_52,X1_52,X0_53,X2_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(k4_tmap_1(X1_52,X2_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
    | r2_hidden(sK1(X1_52,X0_52,X2_52,X0_53,k4_tmap_1(X1_52,X2_52)),u1_struct_0(X2_52)) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_52,X1_52,X0_53,X2_52)) != iProver_top
    | v1_funct_1(k4_tmap_1(X1_52,X2_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2271,c_7489])).

cnf(c_34639,plain,
    ( k2_tmap_1(sK3,sK2,sK4,sK3) = k4_tmap_1(sK2,sK3)
    | v1_funct_2(k2_tmap_1(sK3,sK2,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK1(sK2,sK3,sK3,sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK2,sK4,sK3)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5470,c_7495])).

cnf(c_34640,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | r2_hidden(sK1(sK2,sK3,sK3,sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34639,c_5470])).

cnf(c_34645,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | r2_hidden(sK1(sK2,sK3,sK3,sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
    | ~ v1_funct_1(sK4)
    | k4_tmap_1(sK2,sK3) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_34640])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1649,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ r2_hidden(X2_53,X0_53)
    | ~ v1_xboole_0(X1_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_8961,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0_53))
    | ~ r2_hidden(sK1(sK2,sK3,sK3,sK4,X1_53),u1_struct_0(sK3))
    | ~ v1_xboole_0(X0_53) ),
    inference(instantiation,[status(thm)],[c_1649])).

cnf(c_17736,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK1(sK2,sK3,sK3,sK4,X0_53),u1_struct_0(sK3))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_8961])).

cnf(c_43563,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK1(sK2,sK3,sK3,sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_17736])).

cnf(c_56631,plain,
    ( k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8122,c_35,c_34,c_33,c_32,c_31,c_30,c_41,c_29,c_42,c_28,c_47,c_1675,c_2470,c_2596,c_2757,c_2793,c_3078,c_3139,c_3238,c_3279,c_5053,c_6383,c_8120,c_8334,c_26945,c_34645,c_43563])).

cnf(c_2,plain,
    ( r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1648,plain,
    ( r2_funct_2(X0_53,X1_53,X2_53,X3_53)
    | ~ v1_funct_2(X3_53,X0_53,X1_53)
    | ~ v1_funct_2(X2_53,X0_53,X1_53)
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X2_53)
    | ~ v1_funct_1(X3_53)
    | k1_funct_1(X3_53,sK0(X0_53,X2_53,X3_53)) != k1_funct_1(X2_53,sK0(X0_53,X2_53,X3_53)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2252,plain,
    ( k1_funct_1(X0_53,sK0(X1_53,X2_53,X0_53)) != k1_funct_1(X2_53,sK0(X1_53,X2_53,X0_53))
    | r2_funct_2(X1_53,X3_53,X2_53,X0_53) = iProver_top
    | v1_funct_2(X2_53,X1_53,X3_53) != iProver_top
    | v1_funct_2(X0_53,X1_53,X3_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1648])).

cnf(c_56633,plain,
    ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) != sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
    | r2_funct_2(u1_struct_0(sK3),X0_53,sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),X0_53) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),X0_53) != iProver_top
    | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0_53))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0_53))) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_56631,c_2252])).

cnf(c_27,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | k1_funct_1(sK4,X0) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1623,negated_conjecture,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK2))
    | ~ r2_hidden(X0_53,u1_struct_0(sK3))
    | k1_funct_1(sK4,X0_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_2277,plain,
    ( k1_funct_1(sK4,X0_53) = X0_53
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1623])).

cnf(c_4286,plain,
    ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4281,c_2277])).

cnf(c_4301,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | k1_funct_1(sK4,sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
    | r2_hidden(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4286,c_36,c_38,c_40])).

cnf(c_4302,plain,
    ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4301])).

cnf(c_4305,plain,
    ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4126,c_4302])).

cnf(c_4306,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k1_funct_1(sK4,sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4305])).

cnf(c_56944,plain,
    ( r2_funct_2(u1_struct_0(sK3),X0_53,sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),X0_53) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),X0_53) != iProver_top
    | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0_53))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0_53))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_56633,c_35,c_36,c_34,c_37,c_33,c_38,c_32,c_31,c_40,c_30,c_41,c_29,c_42,c_28,c_47,c_1675,c_2470,c_2596,c_2597,c_2757,c_2793,c_3078,c_3139,c_3238,c_3279,c_4306,c_5053,c_6383,c_8334,c_26945,c_34645,c_43563])).

cnf(c_56950,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2265,c_56944])).

cnf(c_8335,plain,
    ( k4_tmap_1(sK2,sK3) = sK4
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8334])).

cnf(c_3140,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3139])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_56950,c_8335,c_6383,c_5053,c_3279,c_3238,c_3140,c_2758,c_2597,c_1675,c_47,c_43,c_42,c_41,c_40,c_38,c_37,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 39.25/5.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.25/5.49  
% 39.25/5.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.25/5.49  
% 39.25/5.49  ------  iProver source info
% 39.25/5.49  
% 39.25/5.49  git: date: 2020-06-30 10:37:57 +0100
% 39.25/5.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.25/5.49  git: non_committed_changes: false
% 39.25/5.49  git: last_make_outside_of_git: false
% 39.25/5.49  
% 39.25/5.49  ------ 
% 39.25/5.49  
% 39.25/5.49  ------ Input Options
% 39.25/5.49  
% 39.25/5.49  --out_options                           all
% 39.25/5.49  --tptp_safe_out                         true
% 39.25/5.49  --problem_path                          ""
% 39.25/5.49  --include_path                          ""
% 39.25/5.49  --clausifier                            res/vclausify_rel
% 39.25/5.49  --clausifier_options                    ""
% 39.25/5.49  --stdin                                 false
% 39.25/5.49  --stats_out                             all
% 39.25/5.49  
% 39.25/5.49  ------ General Options
% 39.25/5.49  
% 39.25/5.49  --fof                                   false
% 39.25/5.49  --time_out_real                         305.
% 39.25/5.49  --time_out_virtual                      -1.
% 39.25/5.49  --symbol_type_check                     false
% 39.25/5.49  --clausify_out                          false
% 39.25/5.49  --sig_cnt_out                           false
% 39.25/5.49  --trig_cnt_out                          false
% 39.25/5.49  --trig_cnt_out_tolerance                1.
% 39.25/5.49  --trig_cnt_out_sk_spl                   false
% 39.25/5.49  --abstr_cl_out                          false
% 39.25/5.49  
% 39.25/5.49  ------ Global Options
% 39.25/5.49  
% 39.25/5.49  --schedule                              default
% 39.25/5.49  --add_important_lit                     false
% 39.25/5.49  --prop_solver_per_cl                    1000
% 39.25/5.49  --min_unsat_core                        false
% 39.25/5.49  --soft_assumptions                      false
% 39.25/5.49  --soft_lemma_size                       3
% 39.25/5.49  --prop_impl_unit_size                   0
% 39.25/5.49  --prop_impl_unit                        []
% 39.25/5.49  --share_sel_clauses                     true
% 39.25/5.49  --reset_solvers                         false
% 39.25/5.49  --bc_imp_inh                            [conj_cone]
% 39.25/5.49  --conj_cone_tolerance                   3.
% 39.25/5.49  --extra_neg_conj                        none
% 39.25/5.49  --large_theory_mode                     true
% 39.25/5.49  --prolific_symb_bound                   200
% 39.25/5.49  --lt_threshold                          2000
% 39.25/5.49  --clause_weak_htbl                      true
% 39.25/5.49  --gc_record_bc_elim                     false
% 39.25/5.49  
% 39.25/5.49  ------ Preprocessing Options
% 39.25/5.49  
% 39.25/5.49  --preprocessing_flag                    true
% 39.25/5.49  --time_out_prep_mult                    0.1
% 39.25/5.49  --splitting_mode                        input
% 39.25/5.49  --splitting_grd                         true
% 39.25/5.49  --splitting_cvd                         false
% 39.25/5.49  --splitting_cvd_svl                     false
% 39.25/5.49  --splitting_nvd                         32
% 39.25/5.49  --sub_typing                            true
% 39.25/5.49  --prep_gs_sim                           true
% 39.25/5.49  --prep_unflatten                        true
% 39.25/5.49  --prep_res_sim                          true
% 39.25/5.49  --prep_upred                            true
% 39.25/5.49  --prep_sem_filter                       exhaustive
% 39.25/5.49  --prep_sem_filter_out                   false
% 39.25/5.49  --pred_elim                             true
% 39.25/5.49  --res_sim_input                         true
% 39.25/5.49  --eq_ax_congr_red                       true
% 39.25/5.49  --pure_diseq_elim                       true
% 39.25/5.49  --brand_transform                       false
% 39.25/5.49  --non_eq_to_eq                          false
% 39.25/5.49  --prep_def_merge                        true
% 39.25/5.49  --prep_def_merge_prop_impl              false
% 39.25/5.49  --prep_def_merge_mbd                    true
% 39.25/5.49  --prep_def_merge_tr_red                 false
% 39.25/5.49  --prep_def_merge_tr_cl                  false
% 39.25/5.49  --smt_preprocessing                     true
% 39.25/5.49  --smt_ac_axioms                         fast
% 39.25/5.49  --preprocessed_out                      false
% 39.25/5.49  --preprocessed_stats                    false
% 39.25/5.49  
% 39.25/5.49  ------ Abstraction refinement Options
% 39.25/5.49  
% 39.25/5.49  --abstr_ref                             []
% 39.25/5.49  --abstr_ref_prep                        false
% 39.25/5.49  --abstr_ref_until_sat                   false
% 39.25/5.49  --abstr_ref_sig_restrict                funpre
% 39.25/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.25/5.49  --abstr_ref_under                       []
% 39.25/5.49  
% 39.25/5.49  ------ SAT Options
% 39.25/5.49  
% 39.25/5.49  --sat_mode                              false
% 39.25/5.49  --sat_fm_restart_options                ""
% 39.25/5.49  --sat_gr_def                            false
% 39.25/5.49  --sat_epr_types                         true
% 39.25/5.49  --sat_non_cyclic_types                  false
% 39.25/5.49  --sat_finite_models                     false
% 39.25/5.49  --sat_fm_lemmas                         false
% 39.25/5.49  --sat_fm_prep                           false
% 39.25/5.49  --sat_fm_uc_incr                        true
% 39.25/5.49  --sat_out_model                         small
% 39.25/5.49  --sat_out_clauses                       false
% 39.25/5.49  
% 39.25/5.49  ------ QBF Options
% 39.25/5.49  
% 39.25/5.49  --qbf_mode                              false
% 39.25/5.49  --qbf_elim_univ                         false
% 39.25/5.49  --qbf_dom_inst                          none
% 39.25/5.49  --qbf_dom_pre_inst                      false
% 39.25/5.49  --qbf_sk_in                             false
% 39.25/5.49  --qbf_pred_elim                         true
% 39.25/5.49  --qbf_split                             512
% 39.25/5.49  
% 39.25/5.49  ------ BMC1 Options
% 39.25/5.49  
% 39.25/5.49  --bmc1_incremental                      false
% 39.25/5.49  --bmc1_axioms                           reachable_all
% 39.25/5.49  --bmc1_min_bound                        0
% 39.25/5.49  --bmc1_max_bound                        -1
% 39.25/5.49  --bmc1_max_bound_default                -1
% 39.25/5.49  --bmc1_symbol_reachability              true
% 39.25/5.49  --bmc1_property_lemmas                  false
% 39.25/5.49  --bmc1_k_induction                      false
% 39.25/5.49  --bmc1_non_equiv_states                 false
% 39.25/5.49  --bmc1_deadlock                         false
% 39.25/5.49  --bmc1_ucm                              false
% 39.25/5.49  --bmc1_add_unsat_core                   none
% 39.25/5.49  --bmc1_unsat_core_children              false
% 39.25/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.25/5.49  --bmc1_out_stat                         full
% 39.25/5.49  --bmc1_ground_init                      false
% 39.25/5.49  --bmc1_pre_inst_next_state              false
% 39.25/5.49  --bmc1_pre_inst_state                   false
% 39.25/5.49  --bmc1_pre_inst_reach_state             false
% 39.25/5.49  --bmc1_out_unsat_core                   false
% 39.25/5.49  --bmc1_aig_witness_out                  false
% 39.25/5.49  --bmc1_verbose                          false
% 39.25/5.49  --bmc1_dump_clauses_tptp                false
% 39.25/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.25/5.49  --bmc1_dump_file                        -
% 39.25/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.25/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.25/5.49  --bmc1_ucm_extend_mode                  1
% 39.25/5.49  --bmc1_ucm_init_mode                    2
% 39.25/5.49  --bmc1_ucm_cone_mode                    none
% 39.25/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.25/5.49  --bmc1_ucm_relax_model                  4
% 39.25/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.25/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.25/5.49  --bmc1_ucm_layered_model                none
% 39.25/5.49  --bmc1_ucm_max_lemma_size               10
% 39.25/5.49  
% 39.25/5.49  ------ AIG Options
% 39.25/5.49  
% 39.25/5.49  --aig_mode                              false
% 39.25/5.49  
% 39.25/5.49  ------ Instantiation Options
% 39.25/5.49  
% 39.25/5.49  --instantiation_flag                    true
% 39.25/5.49  --inst_sos_flag                         true
% 39.25/5.49  --inst_sos_phase                        true
% 39.25/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.25/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.25/5.49  --inst_lit_sel_side                     num_symb
% 39.25/5.49  --inst_solver_per_active                1400
% 39.25/5.49  --inst_solver_calls_frac                1.
% 39.25/5.49  --inst_passive_queue_type               priority_queues
% 39.25/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.25/5.49  --inst_passive_queues_freq              [25;2]
% 39.25/5.49  --inst_dismatching                      true
% 39.25/5.49  --inst_eager_unprocessed_to_passive     true
% 39.25/5.49  --inst_prop_sim_given                   true
% 39.25/5.49  --inst_prop_sim_new                     false
% 39.25/5.49  --inst_subs_new                         false
% 39.25/5.49  --inst_eq_res_simp                      false
% 39.25/5.49  --inst_subs_given                       false
% 39.25/5.49  --inst_orphan_elimination               true
% 39.25/5.49  --inst_learning_loop_flag               true
% 39.25/5.49  --inst_learning_start                   3000
% 39.25/5.49  --inst_learning_factor                  2
% 39.25/5.49  --inst_start_prop_sim_after_learn       3
% 39.25/5.49  --inst_sel_renew                        solver
% 39.25/5.49  --inst_lit_activity_flag                true
% 39.25/5.49  --inst_restr_to_given                   false
% 39.25/5.49  --inst_activity_threshold               500
% 39.25/5.49  --inst_out_proof                        true
% 39.25/5.49  
% 39.25/5.49  ------ Resolution Options
% 39.25/5.49  
% 39.25/5.49  --resolution_flag                       true
% 39.25/5.49  --res_lit_sel                           adaptive
% 39.25/5.49  --res_lit_sel_side                      none
% 39.25/5.49  --res_ordering                          kbo
% 39.25/5.49  --res_to_prop_solver                    active
% 39.25/5.49  --res_prop_simpl_new                    false
% 39.25/5.49  --res_prop_simpl_given                  true
% 39.25/5.49  --res_passive_queue_type                priority_queues
% 39.25/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.25/5.49  --res_passive_queues_freq               [15;5]
% 39.25/5.49  --res_forward_subs                      full
% 39.25/5.49  --res_backward_subs                     full
% 39.25/5.49  --res_forward_subs_resolution           true
% 39.25/5.49  --res_backward_subs_resolution          true
% 39.25/5.49  --res_orphan_elimination                true
% 39.25/5.49  --res_time_limit                        2.
% 39.25/5.49  --res_out_proof                         true
% 39.25/5.49  
% 39.25/5.49  ------ Superposition Options
% 39.25/5.49  
% 39.25/5.49  --superposition_flag                    true
% 39.25/5.49  --sup_passive_queue_type                priority_queues
% 39.25/5.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.25/5.49  --sup_passive_queues_freq               [8;1;4]
% 39.25/5.49  --demod_completeness_check              fast
% 39.25/5.49  --demod_use_ground                      true
% 39.25/5.49  --sup_to_prop_solver                    passive
% 39.25/5.49  --sup_prop_simpl_new                    true
% 39.25/5.49  --sup_prop_simpl_given                  true
% 39.25/5.49  --sup_fun_splitting                     true
% 39.25/5.49  --sup_smt_interval                      50000
% 39.25/5.49  
% 39.25/5.49  ------ Superposition Simplification Setup
% 39.25/5.49  
% 39.25/5.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.25/5.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.25/5.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.25/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.25/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.25/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.25/5.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.25/5.49  --sup_immed_triv                        [TrivRules]
% 39.25/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.25/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.25/5.49  --sup_immed_bw_main                     []
% 39.25/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.25/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.25/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.25/5.49  --sup_input_bw                          []
% 39.25/5.49  
% 39.25/5.49  ------ Combination Options
% 39.25/5.49  
% 39.25/5.49  --comb_res_mult                         3
% 39.25/5.49  --comb_sup_mult                         2
% 39.25/5.49  --comb_inst_mult                        10
% 39.25/5.49  
% 39.25/5.49  ------ Debug Options
% 39.25/5.49  
% 39.25/5.49  --dbg_backtrace                         false
% 39.25/5.49  --dbg_dump_prop_clauses                 false
% 39.25/5.49  --dbg_dump_prop_clauses_file            -
% 39.25/5.49  --dbg_out_stat                          false
% 39.25/5.49  ------ Parsing...
% 39.25/5.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.25/5.49  
% 39.25/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 39.25/5.49  
% 39.25/5.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.25/5.49  
% 39.25/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.25/5.49  ------ Proving...
% 39.25/5.49  ------ Problem Properties 
% 39.25/5.49  
% 39.25/5.49  
% 39.25/5.49  clauses                                 36
% 39.25/5.49  conjectures                             10
% 39.25/5.49  EPR                                     11
% 39.25/5.49  Horn                                    20
% 39.25/5.49  unary                                   9
% 39.25/5.49  binary                                  1
% 39.25/5.49  lits                                    221
% 39.25/5.49  lits eq                                 8
% 39.25/5.49  fd_pure                                 0
% 39.25/5.49  fd_pseudo                               0
% 39.25/5.49  fd_cond                                 0
% 39.25/5.49  fd_pseudo_cond                          1
% 39.25/5.49  AC symbols                              0
% 39.25/5.49  
% 39.25/5.49  ------ Schedule dynamic 5 is on 
% 39.25/5.49  
% 39.25/5.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.25/5.49  
% 39.25/5.49  
% 39.25/5.49  ------ 
% 39.25/5.49  Current options:
% 39.25/5.49  ------ 
% 39.25/5.49  
% 39.25/5.49  ------ Input Options
% 39.25/5.49  
% 39.25/5.49  --out_options                           all
% 39.25/5.49  --tptp_safe_out                         true
% 39.25/5.49  --problem_path                          ""
% 39.25/5.49  --include_path                          ""
% 39.25/5.49  --clausifier                            res/vclausify_rel
% 39.25/5.49  --clausifier_options                    ""
% 39.25/5.49  --stdin                                 false
% 39.25/5.49  --stats_out                             all
% 39.25/5.49  
% 39.25/5.49  ------ General Options
% 39.25/5.49  
% 39.25/5.49  --fof                                   false
% 39.25/5.49  --time_out_real                         305.
% 39.25/5.49  --time_out_virtual                      -1.
% 39.25/5.49  --symbol_type_check                     false
% 39.25/5.49  --clausify_out                          false
% 39.25/5.49  --sig_cnt_out                           false
% 39.25/5.49  --trig_cnt_out                          false
% 39.25/5.49  --trig_cnt_out_tolerance                1.
% 39.25/5.49  --trig_cnt_out_sk_spl                   false
% 39.25/5.49  --abstr_cl_out                          false
% 39.25/5.49  
% 39.25/5.49  ------ Global Options
% 39.25/5.49  
% 39.25/5.49  --schedule                              default
% 39.25/5.49  --add_important_lit                     false
% 39.25/5.49  --prop_solver_per_cl                    1000
% 39.25/5.49  --min_unsat_core                        false
% 39.25/5.49  --soft_assumptions                      false
% 39.25/5.49  --soft_lemma_size                       3
% 39.25/5.49  --prop_impl_unit_size                   0
% 39.25/5.49  --prop_impl_unit                        []
% 39.25/5.49  --share_sel_clauses                     true
% 39.25/5.49  --reset_solvers                         false
% 39.25/5.49  --bc_imp_inh                            [conj_cone]
% 39.25/5.49  --conj_cone_tolerance                   3.
% 39.25/5.49  --extra_neg_conj                        none
% 39.25/5.49  --large_theory_mode                     true
% 39.25/5.49  --prolific_symb_bound                   200
% 39.25/5.49  --lt_threshold                          2000
% 39.25/5.49  --clause_weak_htbl                      true
% 39.25/5.49  --gc_record_bc_elim                     false
% 39.25/5.49  
% 39.25/5.49  ------ Preprocessing Options
% 39.25/5.49  
% 39.25/5.49  --preprocessing_flag                    true
% 39.25/5.49  --time_out_prep_mult                    0.1
% 39.25/5.49  --splitting_mode                        input
% 39.25/5.49  --splitting_grd                         true
% 39.25/5.49  --splitting_cvd                         false
% 39.25/5.49  --splitting_cvd_svl                     false
% 39.25/5.49  --splitting_nvd                         32
% 39.25/5.49  --sub_typing                            true
% 39.25/5.49  --prep_gs_sim                           true
% 39.25/5.49  --prep_unflatten                        true
% 39.25/5.49  --prep_res_sim                          true
% 39.25/5.49  --prep_upred                            true
% 39.25/5.49  --prep_sem_filter                       exhaustive
% 39.25/5.49  --prep_sem_filter_out                   false
% 39.25/5.49  --pred_elim                             true
% 39.25/5.49  --res_sim_input                         true
% 39.25/5.49  --eq_ax_congr_red                       true
% 39.25/5.49  --pure_diseq_elim                       true
% 39.25/5.49  --brand_transform                       false
% 39.25/5.49  --non_eq_to_eq                          false
% 39.25/5.49  --prep_def_merge                        true
% 39.25/5.49  --prep_def_merge_prop_impl              false
% 39.25/5.49  --prep_def_merge_mbd                    true
% 39.25/5.49  --prep_def_merge_tr_red                 false
% 39.25/5.49  --prep_def_merge_tr_cl                  false
% 39.25/5.49  --smt_preprocessing                     true
% 39.25/5.49  --smt_ac_axioms                         fast
% 39.25/5.49  --preprocessed_out                      false
% 39.25/5.49  --preprocessed_stats                    false
% 39.25/5.49  
% 39.25/5.49  ------ Abstraction refinement Options
% 39.25/5.49  
% 39.25/5.49  --abstr_ref                             []
% 39.25/5.49  --abstr_ref_prep                        false
% 39.25/5.49  --abstr_ref_until_sat                   false
% 39.25/5.49  --abstr_ref_sig_restrict                funpre
% 39.25/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.25/5.49  --abstr_ref_under                       []
% 39.25/5.49  
% 39.25/5.49  ------ SAT Options
% 39.25/5.49  
% 39.25/5.49  --sat_mode                              false
% 39.25/5.49  --sat_fm_restart_options                ""
% 39.25/5.49  --sat_gr_def                            false
% 39.25/5.49  --sat_epr_types                         true
% 39.25/5.49  --sat_non_cyclic_types                  false
% 39.25/5.49  --sat_finite_models                     false
% 39.25/5.49  --sat_fm_lemmas                         false
% 39.25/5.49  --sat_fm_prep                           false
% 39.25/5.49  --sat_fm_uc_incr                        true
% 39.25/5.49  --sat_out_model                         small
% 39.25/5.49  --sat_out_clauses                       false
% 39.25/5.49  
% 39.25/5.49  ------ QBF Options
% 39.25/5.49  
% 39.25/5.49  --qbf_mode                              false
% 39.25/5.49  --qbf_elim_univ                         false
% 39.25/5.49  --qbf_dom_inst                          none
% 39.25/5.49  --qbf_dom_pre_inst                      false
% 39.25/5.49  --qbf_sk_in                             false
% 39.25/5.49  --qbf_pred_elim                         true
% 39.25/5.49  --qbf_split                             512
% 39.25/5.49  
% 39.25/5.49  ------ BMC1 Options
% 39.25/5.49  
% 39.25/5.49  --bmc1_incremental                      false
% 39.25/5.49  --bmc1_axioms                           reachable_all
% 39.25/5.49  --bmc1_min_bound                        0
% 39.25/5.49  --bmc1_max_bound                        -1
% 39.25/5.49  --bmc1_max_bound_default                -1
% 39.25/5.49  --bmc1_symbol_reachability              true
% 39.25/5.49  --bmc1_property_lemmas                  false
% 39.25/5.49  --bmc1_k_induction                      false
% 39.25/5.49  --bmc1_non_equiv_states                 false
% 39.25/5.49  --bmc1_deadlock                         false
% 39.25/5.49  --bmc1_ucm                              false
% 39.25/5.49  --bmc1_add_unsat_core                   none
% 39.25/5.49  --bmc1_unsat_core_children              false
% 39.25/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.25/5.49  --bmc1_out_stat                         full
% 39.25/5.49  --bmc1_ground_init                      false
% 39.25/5.49  --bmc1_pre_inst_next_state              false
% 39.25/5.49  --bmc1_pre_inst_state                   false
% 39.25/5.49  --bmc1_pre_inst_reach_state             false
% 39.25/5.49  --bmc1_out_unsat_core                   false
% 39.25/5.49  --bmc1_aig_witness_out                  false
% 39.25/5.49  --bmc1_verbose                          false
% 39.25/5.49  --bmc1_dump_clauses_tptp                false
% 39.25/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.25/5.49  --bmc1_dump_file                        -
% 39.25/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.25/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.25/5.49  --bmc1_ucm_extend_mode                  1
% 39.25/5.49  --bmc1_ucm_init_mode                    2
% 39.25/5.49  --bmc1_ucm_cone_mode                    none
% 39.25/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.25/5.49  --bmc1_ucm_relax_model                  4
% 39.25/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.25/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.25/5.49  --bmc1_ucm_layered_model                none
% 39.25/5.49  --bmc1_ucm_max_lemma_size               10
% 39.25/5.49  
% 39.25/5.49  ------ AIG Options
% 39.25/5.49  
% 39.25/5.49  --aig_mode                              false
% 39.25/5.49  
% 39.25/5.49  ------ Instantiation Options
% 39.25/5.49  
% 39.25/5.49  --instantiation_flag                    true
% 39.25/5.49  --inst_sos_flag                         true
% 39.25/5.49  --inst_sos_phase                        true
% 39.25/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.25/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.25/5.49  --inst_lit_sel_side                     none
% 39.25/5.49  --inst_solver_per_active                1400
% 39.25/5.49  --inst_solver_calls_frac                1.
% 39.25/5.49  --inst_passive_queue_type               priority_queues
% 39.25/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.25/5.49  --inst_passive_queues_freq              [25;2]
% 39.25/5.49  --inst_dismatching                      true
% 39.25/5.49  --inst_eager_unprocessed_to_passive     true
% 39.25/5.49  --inst_prop_sim_given                   true
% 39.25/5.49  --inst_prop_sim_new                     false
% 39.25/5.49  --inst_subs_new                         false
% 39.25/5.49  --inst_eq_res_simp                      false
% 39.25/5.49  --inst_subs_given                       false
% 39.25/5.49  --inst_orphan_elimination               true
% 39.25/5.49  --inst_learning_loop_flag               true
% 39.25/5.49  --inst_learning_start                   3000
% 39.25/5.49  --inst_learning_factor                  2
% 39.25/5.49  --inst_start_prop_sim_after_learn       3
% 39.25/5.49  --inst_sel_renew                        solver
% 39.25/5.49  --inst_lit_activity_flag                true
% 39.25/5.49  --inst_restr_to_given                   false
% 39.25/5.49  --inst_activity_threshold               500
% 39.25/5.49  --inst_out_proof                        true
% 39.25/5.49  
% 39.25/5.49  ------ Resolution Options
% 39.25/5.49  
% 39.25/5.49  --resolution_flag                       false
% 39.25/5.49  --res_lit_sel                           adaptive
% 39.25/5.49  --res_lit_sel_side                      none
% 39.25/5.49  --res_ordering                          kbo
% 39.25/5.49  --res_to_prop_solver                    active
% 39.25/5.49  --res_prop_simpl_new                    false
% 39.25/5.49  --res_prop_simpl_given                  true
% 39.25/5.49  --res_passive_queue_type                priority_queues
% 39.25/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.25/5.49  --res_passive_queues_freq               [15;5]
% 39.25/5.49  --res_forward_subs                      full
% 39.25/5.49  --res_backward_subs                     full
% 39.25/5.49  --res_forward_subs_resolution           true
% 39.25/5.49  --res_backward_subs_resolution          true
% 39.25/5.49  --res_orphan_elimination                true
% 39.25/5.49  --res_time_limit                        2.
% 39.25/5.49  --res_out_proof                         true
% 39.25/5.49  
% 39.25/5.49  ------ Superposition Options
% 39.25/5.49  
% 39.25/5.49  --superposition_flag                    true
% 39.25/5.49  --sup_passive_queue_type                priority_queues
% 39.25/5.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.25/5.49  --sup_passive_queues_freq               [8;1;4]
% 39.25/5.49  --demod_completeness_check              fast
% 39.25/5.49  --demod_use_ground                      true
% 39.25/5.49  --sup_to_prop_solver                    passive
% 39.25/5.49  --sup_prop_simpl_new                    true
% 39.25/5.49  --sup_prop_simpl_given                  true
% 39.25/5.49  --sup_fun_splitting                     true
% 39.25/5.49  --sup_smt_interval                      50000
% 39.25/5.49  
% 39.25/5.49  ------ Superposition Simplification Setup
% 39.25/5.49  
% 39.25/5.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.25/5.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.25/5.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.25/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.25/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.25/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.25/5.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.25/5.49  --sup_immed_triv                        [TrivRules]
% 39.25/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.25/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.25/5.49  --sup_immed_bw_main                     []
% 39.25/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.25/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.25/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.25/5.49  --sup_input_bw                          []
% 39.25/5.49  
% 39.25/5.49  ------ Combination Options
% 39.25/5.49  
% 39.25/5.49  --comb_res_mult                         3
% 39.25/5.49  --comb_sup_mult                         2
% 39.25/5.49  --comb_inst_mult                        10
% 39.25/5.49  
% 39.25/5.49  ------ Debug Options
% 39.25/5.49  
% 39.25/5.49  --dbg_backtrace                         false
% 39.25/5.49  --dbg_dump_prop_clauses                 false
% 39.25/5.49  --dbg_dump_prop_clauses_file            -
% 39.25/5.49  --dbg_out_stat                          false
% 39.25/5.49  
% 39.25/5.49  
% 39.25/5.49  
% 39.25/5.49  
% 39.25/5.49  ------ Proving...
% 39.25/5.49  
% 39.25/5.49  
% 39.25/5.49  % SZS status Theorem for theBenchmark.p
% 39.25/5.49  
% 39.25/5.49  % SZS output start CNFRefutation for theBenchmark.p
% 39.25/5.49  
% 39.25/5.49  fof(f11,axiom,(
% 39.25/5.49    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 39.25/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.49  
% 39.25/5.49  fof(f38,plain,(
% 39.25/5.49    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 39.25/5.49    inference(ennf_transformation,[],[f11])).
% 39.25/5.49  
% 39.25/5.49  fof(f39,plain,(
% 39.25/5.49    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 39.25/5.49    inference(flattening,[],[f38])).
% 39.25/5.49  
% 39.25/5.49  fof(f80,plain,(
% 39.25/5.49    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.25/5.49    inference(cnf_transformation,[],[f39])).
% 39.25/5.49  
% 39.25/5.49  fof(f18,conjecture,(
% 39.25/5.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 39.25/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.49  
% 39.25/5.49  fof(f19,negated_conjecture,(
% 39.25/5.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 39.25/5.49    inference(negated_conjecture,[],[f18])).
% 39.25/5.49  
% 39.25/5.49  fof(f50,plain,(
% 39.25/5.49    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 39.25/5.49    inference(ennf_transformation,[],[f19])).
% 39.25/5.49  
% 39.25/5.49  fof(f51,plain,(
% 39.25/5.49    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 39.25/5.49    inference(flattening,[],[f50])).
% 39.25/5.49  
% 39.25/5.49  fof(f61,plain,(
% 39.25/5.49    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK4) & ! [X3] : (k1_funct_1(sK4,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 39.25/5.49    introduced(choice_axiom,[])).
% 39.25/5.49  
% 39.25/5.49  fof(f60,plain,(
% 39.25/5.49    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k4_tmap_1(X0,sK3),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 39.25/5.49    introduced(choice_axiom,[])).
% 39.25/5.49  
% 39.25/5.49  fof(f59,plain,(
% 39.25/5.49    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK2),k4_tmap_1(sK2,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 39.25/5.49    introduced(choice_axiom,[])).
% 39.25/5.49  
% 39.25/5.49  fof(f62,plain,(
% 39.25/5.49    ((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) & ! [X3] : (k1_funct_1(sK4,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 39.25/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f51,f61,f60,f59])).
% 39.25/5.49  
% 39.25/5.49  fof(f96,plain,(
% 39.25/5.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 39.25/5.49    inference(cnf_transformation,[],[f62])).
% 39.25/5.49  
% 39.25/5.49  fof(f3,axiom,(
% 39.25/5.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 39.25/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.49  
% 39.25/5.49  fof(f23,plain,(
% 39.25/5.49    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 39.25/5.49    inference(ennf_transformation,[],[f3])).
% 39.25/5.49  
% 39.25/5.49  fof(f24,plain,(
% 39.25/5.49    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 39.25/5.49    inference(flattening,[],[f23])).
% 39.25/5.49  
% 39.25/5.49  fof(f52,plain,(
% 39.25/5.49    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 39.25/5.49    inference(nnf_transformation,[],[f24])).
% 39.25/5.49  
% 39.25/5.49  fof(f53,plain,(
% 39.25/5.49    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 39.25/5.49    inference(rectify,[],[f52])).
% 39.25/5.49  
% 39.25/5.49  fof(f54,plain,(
% 39.25/5.49    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0)))),
% 39.25/5.49    introduced(choice_axiom,[])).
% 39.25/5.49  
% 39.25/5.49  fof(f55,plain,(
% 39.25/5.49    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 39.25/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f53,f54])).
% 39.25/5.49  
% 39.25/5.49  fof(f66,plain,(
% 39.25/5.49    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | m1_subset_1(sK0(X0,X2,X3),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 39.25/5.49    inference(cnf_transformation,[],[f55])).
% 39.25/5.49  
% 39.25/5.49  fof(f94,plain,(
% 39.25/5.49    v1_funct_1(sK4)),
% 39.25/5.49    inference(cnf_transformation,[],[f62])).
% 39.25/5.49  
% 39.25/5.49  fof(f95,plain,(
% 39.25/5.49    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 39.25/5.49    inference(cnf_transformation,[],[f62])).
% 39.25/5.49  
% 39.25/5.49  fof(f89,plain,(
% 39.25/5.49    ~v2_struct_0(sK2)),
% 39.25/5.49    inference(cnf_transformation,[],[f62])).
% 39.25/5.49  
% 39.25/5.49  fof(f90,plain,(
% 39.25/5.49    v2_pre_topc(sK2)),
% 39.25/5.49    inference(cnf_transformation,[],[f62])).
% 39.25/5.49  
% 39.25/5.49  fof(f91,plain,(
% 39.25/5.49    l1_pre_topc(sK2)),
% 39.25/5.49    inference(cnf_transformation,[],[f62])).
% 39.25/5.49  
% 39.25/5.49  fof(f93,plain,(
% 39.25/5.49    m1_pre_topc(sK3,sK2)),
% 39.25/5.49    inference(cnf_transformation,[],[f62])).
% 39.25/5.49  
% 39.25/5.49  fof(f78,plain,(
% 39.25/5.49    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.25/5.49    inference(cnf_transformation,[],[f39])).
% 39.25/5.49  
% 39.25/5.49  fof(f79,plain,(
% 39.25/5.49    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.25/5.49    inference(cnf_transformation,[],[f39])).
% 39.25/5.49  
% 39.25/5.49  fof(f1,axiom,(
% 39.25/5.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 39.25/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.49  
% 39.25/5.49  fof(f20,plain,(
% 39.25/5.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 39.25/5.49    inference(ennf_transformation,[],[f1])).
% 39.25/5.49  
% 39.25/5.49  fof(f21,plain,(
% 39.25/5.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 39.25/5.49    inference(flattening,[],[f20])).
% 39.25/5.49  
% 39.25/5.49  fof(f63,plain,(
% 39.25/5.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 39.25/5.49    inference(cnf_transformation,[],[f21])).
% 39.25/5.49  
% 39.25/5.49  fof(f7,axiom,(
% 39.25/5.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 39.25/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.49  
% 39.25/5.49  fof(f30,plain,(
% 39.25/5.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 39.25/5.50    inference(ennf_transformation,[],[f7])).
% 39.25/5.50  
% 39.25/5.50  fof(f31,plain,(
% 39.25/5.50    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 39.25/5.50    inference(flattening,[],[f30])).
% 39.25/5.50  
% 39.25/5.50  fof(f72,plain,(
% 39.25/5.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.25/5.50    inference(cnf_transformation,[],[f31])).
% 39.25/5.50  
% 39.25/5.50  fof(f92,plain,(
% 39.25/5.50    ~v2_struct_0(sK3)),
% 39.25/5.50    inference(cnf_transformation,[],[f62])).
% 39.25/5.50  
% 39.25/5.50  fof(f6,axiom,(
% 39.25/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 39.25/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.50  
% 39.25/5.50  fof(f29,plain,(
% 39.25/5.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 39.25/5.50    inference(ennf_transformation,[],[f6])).
% 39.25/5.50  
% 39.25/5.50  fof(f71,plain,(
% 39.25/5.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 39.25/5.50    inference(cnf_transformation,[],[f29])).
% 39.25/5.50  
% 39.25/5.50  fof(f17,axiom,(
% 39.25/5.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 39.25/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.50  
% 39.25/5.50  fof(f48,plain,(
% 39.25/5.50    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 39.25/5.50    inference(ennf_transformation,[],[f17])).
% 39.25/5.50  
% 39.25/5.50  fof(f49,plain,(
% 39.25/5.50    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 39.25/5.50    inference(flattening,[],[f48])).
% 39.25/5.50  
% 39.25/5.50  fof(f88,plain,(
% 39.25/5.50    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.25/5.50    inference(cnf_transformation,[],[f49])).
% 39.25/5.50  
% 39.25/5.50  fof(f4,axiom,(
% 39.25/5.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 39.25/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.50  
% 39.25/5.50  fof(f25,plain,(
% 39.25/5.50    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 39.25/5.50    inference(ennf_transformation,[],[f4])).
% 39.25/5.50  
% 39.25/5.50  fof(f26,plain,(
% 39.25/5.50    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 39.25/5.50    inference(flattening,[],[f25])).
% 39.25/5.50  
% 39.25/5.50  fof(f56,plain,(
% 39.25/5.50    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 39.25/5.50    inference(nnf_transformation,[],[f26])).
% 39.25/5.50  
% 39.25/5.50  fof(f68,plain,(
% 39.25/5.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 39.25/5.50    inference(cnf_transformation,[],[f56])).
% 39.25/5.50  
% 39.25/5.50  fof(f98,plain,(
% 39.25/5.50    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4)),
% 39.25/5.50    inference(cnf_transformation,[],[f62])).
% 39.25/5.50  
% 39.25/5.50  fof(f5,axiom,(
% 39.25/5.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 39.25/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.50  
% 39.25/5.50  fof(f27,plain,(
% 39.25/5.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 39.25/5.50    inference(ennf_transformation,[],[f5])).
% 39.25/5.50  
% 39.25/5.50  fof(f28,plain,(
% 39.25/5.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 39.25/5.50    inference(flattening,[],[f27])).
% 39.25/5.50  
% 39.25/5.50  fof(f70,plain,(
% 39.25/5.50    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 39.25/5.50    inference(cnf_transformation,[],[f28])).
% 39.25/5.50  
% 39.25/5.50  fof(f13,axiom,(
% 39.25/5.50    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 39.25/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.50  
% 39.25/5.50  fof(f41,plain,(
% 39.25/5.50    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 39.25/5.50    inference(ennf_transformation,[],[f13])).
% 39.25/5.50  
% 39.25/5.50  fof(f82,plain,(
% 39.25/5.50    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 39.25/5.50    inference(cnf_transformation,[],[f41])).
% 39.25/5.50  
% 39.25/5.50  fof(f69,plain,(
% 39.25/5.50    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 39.25/5.50    inference(cnf_transformation,[],[f56])).
% 39.25/5.50  
% 39.25/5.50  fof(f99,plain,(
% 39.25/5.50    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 39.25/5.50    inference(equality_resolution,[],[f69])).
% 39.25/5.50  
% 39.25/5.50  fof(f12,axiom,(
% 39.25/5.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 39.25/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.50  
% 39.25/5.50  fof(f40,plain,(
% 39.25/5.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 39.25/5.50    inference(ennf_transformation,[],[f12])).
% 39.25/5.50  
% 39.25/5.50  fof(f81,plain,(
% 39.25/5.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 39.25/5.50    inference(cnf_transformation,[],[f40])).
% 39.25/5.50  
% 39.25/5.50  fof(f9,axiom,(
% 39.25/5.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 39.25/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.50  
% 39.25/5.50  fof(f34,plain,(
% 39.25/5.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 39.25/5.50    inference(ennf_transformation,[],[f9])).
% 39.25/5.50  
% 39.25/5.50  fof(f35,plain,(
% 39.25/5.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 39.25/5.50    inference(flattening,[],[f34])).
% 39.25/5.50  
% 39.25/5.50  fof(f74,plain,(
% 39.25/5.50    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.25/5.50    inference(cnf_transformation,[],[f35])).
% 39.25/5.50  
% 39.25/5.50  fof(f8,axiom,(
% 39.25/5.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 39.25/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.50  
% 39.25/5.50  fof(f32,plain,(
% 39.25/5.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 39.25/5.50    inference(ennf_transformation,[],[f8])).
% 39.25/5.50  
% 39.25/5.50  fof(f33,plain,(
% 39.25/5.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 39.25/5.50    inference(flattening,[],[f32])).
% 39.25/5.50  
% 39.25/5.50  fof(f73,plain,(
% 39.25/5.50    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.25/5.50    inference(cnf_transformation,[],[f33])).
% 39.25/5.50  
% 39.25/5.50  fof(f10,axiom,(
% 39.25/5.50    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 39.25/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.50  
% 39.25/5.50  fof(f36,plain,(
% 39.25/5.50    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 39.25/5.50    inference(ennf_transformation,[],[f10])).
% 39.25/5.50  
% 39.25/5.50  fof(f37,plain,(
% 39.25/5.50    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 39.25/5.50    inference(flattening,[],[f36])).
% 39.25/5.50  
% 39.25/5.50  fof(f77,plain,(
% 39.25/5.50    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.25/5.50    inference(cnf_transformation,[],[f37])).
% 39.25/5.50  
% 39.25/5.50  fof(f15,axiom,(
% 39.25/5.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 39.25/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.50  
% 39.25/5.50  fof(f44,plain,(
% 39.25/5.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 39.25/5.50    inference(ennf_transformation,[],[f15])).
% 39.25/5.50  
% 39.25/5.50  fof(f45,plain,(
% 39.25/5.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 39.25/5.50    inference(flattening,[],[f44])).
% 39.25/5.50  
% 39.25/5.50  fof(f86,plain,(
% 39.25/5.50    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.25/5.50    inference(cnf_transformation,[],[f45])).
% 39.25/5.50  
% 39.25/5.50  fof(f76,plain,(
% 39.25/5.50    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.25/5.50    inference(cnf_transformation,[],[f37])).
% 39.25/5.50  
% 39.25/5.50  fof(f75,plain,(
% 39.25/5.50    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.25/5.50    inference(cnf_transformation,[],[f37])).
% 39.25/5.50  
% 39.25/5.50  fof(f14,axiom,(
% 39.25/5.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 39.25/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.50  
% 39.25/5.50  fof(f42,plain,(
% 39.25/5.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k1_funct_1(X4,X5) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 39.25/5.50    inference(ennf_transformation,[],[f14])).
% 39.25/5.50  
% 39.25/5.50  fof(f43,plain,(
% 39.25/5.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k1_funct_1(X4,X5) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 39.25/5.50    inference(flattening,[],[f42])).
% 39.25/5.50  
% 39.25/5.50  fof(f57,plain,(
% 39.25/5.50    ! [X4,X3,X2,X1,X0] : (? [X5] : (k1_funct_1(X4,X5) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) => (k1_funct_1(X4,sK1(X0,X1,X2,X3,X4)) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK1(X0,X1,X2,X3,X4)) & r2_hidden(sK1(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4),u1_struct_0(X1))))),
% 39.25/5.50    introduced(choice_axiom,[])).
% 39.25/5.50  
% 39.25/5.50  fof(f58,plain,(
% 39.25/5.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | (k1_funct_1(X4,sK1(X0,X1,X2,X3,X4)) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK1(X0,X1,X2,X3,X4)) & r2_hidden(sK1(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK1(X0,X1,X2,X3,X4),u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 39.25/5.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f57])).
% 39.25/5.50  
% 39.25/5.50  fof(f84,plain,(
% 39.25/5.50    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | r2_hidden(sK1(X0,X1,X2,X3,X4),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 39.25/5.50    inference(cnf_transformation,[],[f58])).
% 39.25/5.50  
% 39.25/5.50  fof(f2,axiom,(
% 39.25/5.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 39.25/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.25/5.50  
% 39.25/5.50  fof(f22,plain,(
% 39.25/5.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 39.25/5.50    inference(ennf_transformation,[],[f2])).
% 39.25/5.50  
% 39.25/5.50  fof(f64,plain,(
% 39.25/5.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 39.25/5.50    inference(cnf_transformation,[],[f22])).
% 39.25/5.50  
% 39.25/5.50  fof(f67,plain,(
% 39.25/5.50    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 39.25/5.50    inference(cnf_transformation,[],[f55])).
% 39.25/5.50  
% 39.25/5.50  fof(f97,plain,(
% 39.25/5.50    ( ! [X3] : (k1_funct_1(sK4,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK2))) )),
% 39.25/5.50    inference(cnf_transformation,[],[f62])).
% 39.25/5.50  
% 39.25/5.50  cnf(c_15,plain,
% 39.25/5.50      ( ~ m1_pre_topc(X0,X1)
% 39.25/5.50      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 39.25/5.50      | v2_struct_0(X1)
% 39.25/5.50      | ~ l1_pre_topc(X1)
% 39.25/5.50      | ~ v2_pre_topc(X1) ),
% 39.25/5.50      inference(cnf_transformation,[],[f80]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1635,plain,
% 39.25/5.50      ( ~ m1_pre_topc(X0_52,X1_52)
% 39.25/5.50      | m1_subset_1(k4_tmap_1(X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 39.25/5.50      | v2_struct_0(X1_52)
% 39.25/5.50      | ~ l1_pre_topc(X1_52)
% 39.25/5.50      | ~ v2_pre_topc(X1_52) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_15]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2265,plain,
% 39.25/5.50      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 39.25/5.50      | m1_subset_1(k4_tmap_1(X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) = iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X1_52) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1635]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_28,negated_conjecture,
% 39.25/5.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 39.25/5.50      inference(cnf_transformation,[],[f96]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1622,negated_conjecture,
% 39.25/5.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_28]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2278,plain,
% 39.25/5.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1622]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_3,plain,
% 39.25/5.50      ( r2_funct_2(X0,X1,X2,X3)
% 39.25/5.50      | ~ v1_funct_2(X3,X0,X1)
% 39.25/5.50      | ~ v1_funct_2(X2,X0,X1)
% 39.25/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.25/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.25/5.50      | m1_subset_1(sK0(X0,X2,X3),X0)
% 39.25/5.50      | ~ v1_funct_1(X3)
% 39.25/5.50      | ~ v1_funct_1(X2) ),
% 39.25/5.50      inference(cnf_transformation,[],[f66]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1647,plain,
% 39.25/5.50      ( r2_funct_2(X0_53,X1_53,X2_53,X3_53)
% 39.25/5.50      | ~ v1_funct_2(X3_53,X0_53,X1_53)
% 39.25/5.50      | ~ v1_funct_2(X2_53,X0_53,X1_53)
% 39.25/5.50      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 39.25/5.50      | ~ m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 39.25/5.50      | m1_subset_1(sK0(X0_53,X2_53,X3_53),X0_53)
% 39.25/5.50      | ~ v1_funct_1(X2_53)
% 39.25/5.50      | ~ v1_funct_1(X3_53) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_3]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2253,plain,
% 39.25/5.50      ( r2_funct_2(X0_53,X1_53,X2_53,X3_53) = iProver_top
% 39.25/5.50      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 39.25/5.50      | v1_funct_2(X3_53,X0_53,X1_53) != iProver_top
% 39.25/5.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 39.25/5.50      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 39.25/5.50      | m1_subset_1(sK0(X0_53,X2_53,X3_53),X0_53) = iProver_top
% 39.25/5.50      | v1_funct_1(X2_53) != iProver_top
% 39.25/5.50      | v1_funct_1(X3_53) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1647]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_3875,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,X0_53) = iProver_top
% 39.25/5.50      | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | m1_subset_1(sK0(u1_struct_0(sK3),sK4,X0_53),u1_struct_0(sK3)) = iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top
% 39.25/5.50      | v1_funct_1(sK4) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_2278,c_2253]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_30,negated_conjecture,
% 39.25/5.50      ( v1_funct_1(sK4) ),
% 39.25/5.50      inference(cnf_transformation,[],[f94]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_41,plain,
% 39.25/5.50      ( v1_funct_1(sK4) = iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_29,negated_conjecture,
% 39.25/5.50      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 39.25/5.50      inference(cnf_transformation,[],[f95]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_42,plain,
% 39.25/5.50      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4035,plain,
% 39.25/5.50      ( v1_funct_1(X0_53) != iProver_top
% 39.25/5.50      | m1_subset_1(sK0(u1_struct_0(sK3),sK4,X0_53),u1_struct_0(sK3)) = iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,X0_53) = iProver_top
% 39.25/5.50      | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_3875,c_41,c_42]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4036,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,X0_53) = iProver_top
% 39.25/5.50      | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | m1_subset_1(sK0(u1_struct_0(sK3),sK4,X0_53),u1_struct_0(sK3)) = iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top ),
% 39.25/5.50      inference(renaming,[status(thm)],[c_4035]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4040,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_2265,c_4036]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_35,negated_conjecture,
% 39.25/5.50      ( ~ v2_struct_0(sK2) ),
% 39.25/5.50      inference(cnf_transformation,[],[f89]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_36,plain,
% 39.25/5.50      ( v2_struct_0(sK2) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_34,negated_conjecture,
% 39.25/5.50      ( v2_pre_topc(sK2) ),
% 39.25/5.50      inference(cnf_transformation,[],[f90]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_37,plain,
% 39.25/5.50      ( v2_pre_topc(sK2) = iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_33,negated_conjecture,
% 39.25/5.50      ( l1_pre_topc(sK2) ),
% 39.25/5.50      inference(cnf_transformation,[],[f91]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_38,plain,
% 39.25/5.50      ( l1_pre_topc(sK2) = iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_31,negated_conjecture,
% 39.25/5.50      ( m1_pre_topc(sK3,sK2) ),
% 39.25/5.50      inference(cnf_transformation,[],[f93]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_40,plain,
% 39.25/5.50      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_17,plain,
% 39.25/5.50      ( ~ m1_pre_topc(X0,X1)
% 39.25/5.50      | v2_struct_0(X1)
% 39.25/5.50      | ~ l1_pre_topc(X1)
% 39.25/5.50      | ~ v2_pre_topc(X1)
% 39.25/5.50      | v1_funct_1(k4_tmap_1(X1,X0)) ),
% 39.25/5.50      inference(cnf_transformation,[],[f78]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1633,plain,
% 39.25/5.50      ( ~ m1_pre_topc(X0_52,X1_52)
% 39.25/5.50      | v2_struct_0(X1_52)
% 39.25/5.50      | ~ l1_pre_topc(X1_52)
% 39.25/5.50      | ~ v2_pre_topc(X1_52)
% 39.25/5.50      | v1_funct_1(k4_tmap_1(X1_52,X0_52)) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_17]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2596,plain,
% 39.25/5.50      ( ~ m1_pre_topc(sK3,sK2)
% 39.25/5.50      | v2_struct_0(sK2)
% 39.25/5.50      | ~ l1_pre_topc(sK2)
% 39.25/5.50      | ~ v2_pre_topc(sK2)
% 39.25/5.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_1633]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2597,plain,
% 39.25/5.50      ( m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) = iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_2596]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_16,plain,
% 39.25/5.50      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 39.25/5.50      | ~ m1_pre_topc(X1,X0)
% 39.25/5.50      | v2_struct_0(X0)
% 39.25/5.50      | ~ l1_pre_topc(X0)
% 39.25/5.50      | ~ v2_pre_topc(X0) ),
% 39.25/5.50      inference(cnf_transformation,[],[f79]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1634,plain,
% 39.25/5.50      ( v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52))
% 39.25/5.50      | ~ m1_pre_topc(X1_52,X0_52)
% 39.25/5.50      | v2_struct_0(X0_52)
% 39.25/5.50      | ~ l1_pre_topc(X0_52)
% 39.25/5.50      | ~ v2_pre_topc(X0_52) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_16]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2757,plain,
% 39.25/5.50      ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
% 39.25/5.50      | ~ m1_pre_topc(sK3,sK2)
% 39.25/5.50      | v2_struct_0(sK2)
% 39.25/5.50      | ~ l1_pre_topc(sK2)
% 39.25/5.50      | ~ v2_pre_topc(sK2) ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_1634]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2758,plain,
% 39.25/5.50      ( v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_2757]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4120,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_4040,c_36,c_37,c_38,c_40,c_2597,c_2758]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_0,plain,
% 39.25/5.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 39.25/5.50      inference(cnf_transformation,[],[f63]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1650,plain,
% 39.25/5.50      ( ~ m1_subset_1(X0_53,X1_53)
% 39.25/5.50      | r2_hidden(X0_53,X1_53)
% 39.25/5.50      | v1_xboole_0(X1_53) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_0]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2250,plain,
% 39.25/5.50      ( m1_subset_1(X0_53,X1_53) != iProver_top
% 39.25/5.50      | r2_hidden(X0_53,X1_53) = iProver_top
% 39.25/5.50      | v1_xboole_0(X1_53) = iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1650]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4126,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | r2_hidden(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top
% 39.25/5.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_4120,c_2250]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1619,negated_conjecture,
% 39.25/5.50      ( m1_pre_topc(sK3,sK2) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_31]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2281,plain,
% 39.25/5.50      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1619]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_9,plain,
% 39.25/5.50      ( ~ m1_pre_topc(X0,X1)
% 39.25/5.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 39.25/5.50      | m1_subset_1(X2,u1_struct_0(X1))
% 39.25/5.50      | v2_struct_0(X1)
% 39.25/5.50      | v2_struct_0(X0)
% 39.25/5.50      | ~ l1_pre_topc(X1) ),
% 39.25/5.50      inference(cnf_transformation,[],[f72]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1641,plain,
% 39.25/5.50      ( ~ m1_pre_topc(X0_52,X1_52)
% 39.25/5.50      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 39.25/5.50      | m1_subset_1(X0_53,u1_struct_0(X1_52))
% 39.25/5.50      | v2_struct_0(X1_52)
% 39.25/5.50      | v2_struct_0(X0_52)
% 39.25/5.50      | ~ l1_pre_topc(X1_52) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_9]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2259,plain,
% 39.25/5.50      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,u1_struct_0(X1_52)) = iProver_top
% 39.25/5.50      | v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1641]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4125,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,X0_52) != iProver_top
% 39.25/5.50      | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X0_52)) = iProver_top
% 39.25/5.50      | v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | v2_struct_0(sK3) = iProver_top
% 39.25/5.50      | l1_pre_topc(X0_52) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_4120,c_2259]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_32,negated_conjecture,
% 39.25/5.50      ( ~ v2_struct_0(sK3) ),
% 39.25/5.50      inference(cnf_transformation,[],[f92]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_39,plain,
% 39.25/5.50      ( v2_struct_0(sK3) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4280,plain,
% 39.25/5.50      ( v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X0_52)) = iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,X0_52) != iProver_top
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | l1_pre_topc(X0_52) != iProver_top ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_4125,c_39]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4281,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,X0_52) != iProver_top
% 39.25/5.50      | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X0_52)) = iProver_top
% 39.25/5.50      | v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X0_52) != iProver_top ),
% 39.25/5.50      inference(renaming,[status(thm)],[c_4280]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4288,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,X0_52) != iProver_top
% 39.25/5.50      | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X1_52)) = iProver_top
% 39.25/5.50      | v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X0_52) != iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_4281,c_2259]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_8,plain,
% 39.25/5.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 39.25/5.50      inference(cnf_transformation,[],[f71]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1642,plain,
% 39.25/5.50      ( ~ m1_pre_topc(X0_52,X1_52)
% 39.25/5.50      | ~ l1_pre_topc(X1_52)
% 39.25/5.50      | l1_pre_topc(X0_52) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_8]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1696,plain,
% 39.25/5.50      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | l1_pre_topc(X0_52) = iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1642]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_7648,plain,
% 39.25/5.50      ( v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X1_52)) = iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,X0_52) != iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_4288,c_1696]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_7649,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,X0_52) != iProver_top
% 39.25/5.50      | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X1_52)) = iProver_top
% 39.25/5.50      | v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top ),
% 39.25/5.50      inference(renaming,[status(thm)],[c_7648]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_7652,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,sK3) != iProver_top
% 39.25/5.50      | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | v2_struct_0(sK3) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_2281,c_7649]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4283,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_4281]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_7656,plain,
% 39.25/5.50      ( m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_7652,c_36,c_38,c_40,c_4283]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_7657,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | m1_subset_1(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
% 39.25/5.50      inference(renaming,[status(thm)],[c_7656]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_25,plain,
% 39.25/5.50      ( ~ m1_pre_topc(X0,X1)
% 39.25/5.50      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 39.25/5.50      | ~ r2_hidden(X2,u1_struct_0(X0))
% 39.25/5.50      | v2_struct_0(X1)
% 39.25/5.50      | v2_struct_0(X0)
% 39.25/5.50      | ~ l1_pre_topc(X1)
% 39.25/5.50      | ~ v2_pre_topc(X1)
% 39.25/5.50      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
% 39.25/5.50      inference(cnf_transformation,[],[f88]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1625,plain,
% 39.25/5.50      ( ~ m1_pre_topc(X0_52,X1_52)
% 39.25/5.50      | ~ m1_subset_1(X0_53,u1_struct_0(X1_52))
% 39.25/5.50      | ~ r2_hidden(X0_53,u1_struct_0(X0_52))
% 39.25/5.50      | v2_struct_0(X1_52)
% 39.25/5.50      | v2_struct_0(X0_52)
% 39.25/5.50      | ~ l1_pre_topc(X1_52)
% 39.25/5.50      | ~ v2_pre_topc(X1_52)
% 39.25/5.50      | k1_funct_1(k4_tmap_1(X1_52,X0_52),X0_53) = X0_53 ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_25]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2275,plain,
% 39.25/5.50      ( k1_funct_1(k4_tmap_1(X0_52,X1_52),X0_53) = X0_53
% 39.25/5.50      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 39.25/5.50      | r2_hidden(X0_53,u1_struct_0(X1_52)) != iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X0_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X0_52) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1625]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_7661,plain,
% 39.25/5.50      ( k1_funct_1(k4_tmap_1(sK2,X0_52),sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,sK2) != iProver_top
% 39.25/5.50      | r2_hidden(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X0_52)) != iProver_top
% 39.25/5.50      | v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_7657,c_2275]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_7857,plain,
% 39.25/5.50      ( v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | r2_hidden(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X0_52)) != iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,sK2) != iProver_top
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | k1_funct_1(k4_tmap_1(sK2,X0_52),sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)) ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_7661,c_36,c_37,c_38]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_7858,plain,
% 39.25/5.50      ( k1_funct_1(k4_tmap_1(sK2,X0_52),sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,sK2) != iProver_top
% 39.25/5.50      | r2_hidden(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(X0_52)) != iProver_top
% 39.25/5.50      | v2_struct_0(X0_52) = iProver_top ),
% 39.25/5.50      inference(renaming,[status(thm)],[c_7857]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_7864,plain,
% 39.25/5.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | v2_struct_0(sK3) = iProver_top
% 39.25/5.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_4126,c_7858]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_8118,plain,
% 39.25/5.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_7864,c_39,c_40]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_6,plain,
% 39.25/5.50      ( ~ r2_funct_2(X0,X1,X2,X3)
% 39.25/5.50      | ~ v1_funct_2(X3,X0,X1)
% 39.25/5.50      | ~ v1_funct_2(X2,X0,X1)
% 39.25/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.25/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.25/5.50      | ~ v1_funct_1(X3)
% 39.25/5.50      | ~ v1_funct_1(X2)
% 39.25/5.50      | X3 = X2 ),
% 39.25/5.50      inference(cnf_transformation,[],[f68]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1644,plain,
% 39.25/5.50      ( ~ r2_funct_2(X0_53,X1_53,X2_53,X3_53)
% 39.25/5.50      | ~ v1_funct_2(X3_53,X0_53,X1_53)
% 39.25/5.50      | ~ v1_funct_2(X2_53,X0_53,X1_53)
% 39.25/5.50      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 39.25/5.50      | ~ m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 39.25/5.50      | ~ v1_funct_1(X2_53)
% 39.25/5.50      | ~ v1_funct_1(X3_53)
% 39.25/5.50      | X3_53 = X2_53 ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_6]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2256,plain,
% 39.25/5.50      ( X0_53 = X1_53
% 39.25/5.50      | r2_funct_2(X2_53,X3_53,X1_53,X0_53) != iProver_top
% 39.25/5.50      | v1_funct_2(X1_53,X2_53,X3_53) != iProver_top
% 39.25/5.50      | v1_funct_2(X0_53,X2_53,X3_53) != iProver_top
% 39.25/5.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 39.25/5.50      | v1_funct_1(X1_53) != iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1644]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_3882,plain,
% 39.25/5.50      ( k4_tmap_1(X0_52,X1_52) = X0_53
% 39.25/5.50      | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_53,k4_tmap_1(X0_52,X1_52)) != iProver_top
% 39.25/5.50      | v1_funct_2(X0_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 39.25/5.50      | v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 39.25/5.50      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 39.25/5.50      | v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X0_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X0_52) != iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top
% 39.25/5.50      | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_2265,c_2256]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1714,plain,
% 39.25/5.50      ( v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) = iProver_top
% 39.25/5.50      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 39.25/5.50      | v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X0_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X0_52) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1634]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_7488,plain,
% 39.25/5.50      ( v1_funct_2(X0_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 39.25/5.50      | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_53,k4_tmap_1(X0_52,X1_52)) != iProver_top
% 39.25/5.50      | k4_tmap_1(X0_52,X1_52) = X0_53
% 39.25/5.50      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 39.25/5.50      | v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X0_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X0_52) != iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top
% 39.25/5.50      | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_3882,c_1714]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_7489,plain,
% 39.25/5.50      ( k4_tmap_1(X0_52,X1_52) = X0_53
% 39.25/5.50      | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_53,k4_tmap_1(X0_52,X1_52)) != iProver_top
% 39.25/5.50      | v1_funct_2(X0_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 39.25/5.50      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 39.25/5.50      | v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X0_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X0_52) != iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top
% 39.25/5.50      | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
% 39.25/5.50      inference(renaming,[status(thm)],[c_7488]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_8122,plain,
% 39.25/5.50      ( k4_tmap_1(sK2,sK3) = sK4
% 39.25/5.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
% 39.25/5.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 39.25/5.50      | v1_funct_1(sK4) != iProver_top
% 39.25/5.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_8118,c_7489]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_26,negated_conjecture,
% 39.25/5.50      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) ),
% 39.25/5.50      inference(cnf_transformation,[],[f98]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_47,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1652,plain,( X0_53 = X0_53 ),theory(equality) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1675,plain,
% 39.25/5.50      ( sK4 = sK4 ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_1652]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2468,plain,
% 39.25/5.50      ( ~ m1_pre_topc(sK3,X0_52)
% 39.25/5.50      | ~ l1_pre_topc(X0_52)
% 39.25/5.50      | l1_pre_topc(sK3) ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_1642]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2470,plain,
% 39.25/5.50      ( ~ m1_pre_topc(sK3,sK2) | ~ l1_pre_topc(sK2) | l1_pre_topc(sK3) ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_2468]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_7,plain,
% 39.25/5.50      ( ~ m1_pre_topc(X0,X1)
% 39.25/5.50      | ~ l1_pre_topc(X1)
% 39.25/5.50      | ~ v2_pre_topc(X1)
% 39.25/5.50      | v2_pre_topc(X0) ),
% 39.25/5.50      inference(cnf_transformation,[],[f70]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1643,plain,
% 39.25/5.50      ( ~ m1_pre_topc(X0_52,X1_52)
% 39.25/5.50      | ~ l1_pre_topc(X1_52)
% 39.25/5.50      | ~ v2_pre_topc(X1_52)
% 39.25/5.50      | v2_pre_topc(X0_52) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_7]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2791,plain,
% 39.25/5.50      ( ~ m1_pre_topc(sK3,X0_52)
% 39.25/5.50      | ~ l1_pre_topc(X0_52)
% 39.25/5.50      | ~ v2_pre_topc(X0_52)
% 39.25/5.50      | v2_pre_topc(sK3) ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_1643]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2793,plain,
% 39.25/5.50      ( ~ m1_pre_topc(sK3,sK2)
% 39.25/5.50      | ~ l1_pre_topc(sK2)
% 39.25/5.50      | ~ v2_pre_topc(sK2)
% 39.25/5.50      | v2_pre_topc(sK3) ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_2791]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_19,plain,
% 39.25/5.50      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 39.25/5.50      inference(cnf_transformation,[],[f82]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1631,plain,
% 39.25/5.50      ( m1_pre_topc(X0_52,X0_52) | ~ l1_pre_topc(X0_52) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_19]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_3078,plain,
% 39.25/5.50      ( m1_pre_topc(sK3,sK3) | ~ l1_pre_topc(sK3) ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_1631]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_3139,plain,
% 39.25/5.50      ( ~ m1_pre_topc(sK3,sK2)
% 39.25/5.50      | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 39.25/5.50      | v2_struct_0(sK2)
% 39.25/5.50      | ~ l1_pre_topc(sK2)
% 39.25/5.50      | ~ v2_pre_topc(sK2) ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_1635]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_3238,plain,
% 39.25/5.50      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_1652]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_5,plain,
% 39.25/5.50      ( r2_funct_2(X0,X1,X2,X2)
% 39.25/5.50      | ~ v1_funct_2(X2,X0,X1)
% 39.25/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.25/5.50      | ~ v1_funct_1(X2) ),
% 39.25/5.50      inference(cnf_transformation,[],[f99]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1645,plain,
% 39.25/5.50      ( r2_funct_2(X0_53,X1_53,X2_53,X2_53)
% 39.25/5.50      | ~ v1_funct_2(X2_53,X0_53,X1_53)
% 39.25/5.50      | ~ m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 39.25/5.50      | ~ v1_funct_1(X2_53) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_5]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2255,plain,
% 39.25/5.50      ( r2_funct_2(X0_53,X1_53,X2_53,X2_53) = iProver_top
% 39.25/5.50      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 39.25/5.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 39.25/5.50      | v1_funct_1(X2_53) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1645]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_3279,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,sK4) = iProver_top
% 39.25/5.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | v1_funct_1(sK4) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_2278,c_2255]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1657,plain,
% 39.25/5.50      ( ~ r2_funct_2(X0_53,X1_53,X2_53,X3_53)
% 39.25/5.50      | r2_funct_2(X4_53,X5_53,X6_53,X7_53)
% 39.25/5.50      | X4_53 != X0_53
% 39.25/5.50      | X5_53 != X1_53
% 39.25/5.50      | X6_53 != X2_53
% 39.25/5.50      | X7_53 != X3_53 ),
% 39.25/5.50      theory(equality) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2453,plain,
% 39.25/5.50      ( ~ r2_funct_2(X0_53,X1_53,X2_53,X3_53)
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4)
% 39.25/5.50      | k4_tmap_1(sK2,sK3) != X2_53
% 39.25/5.50      | u1_struct_0(sK2) != X1_53
% 39.25/5.50      | u1_struct_0(sK3) != X0_53
% 39.25/5.50      | sK4 != X3_53 ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_1657]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2646,plain,
% 39.25/5.50      ( ~ r2_funct_2(X0_53,u1_struct_0(sK2),X1_53,X2_53)
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4)
% 39.25/5.50      | k4_tmap_1(sK2,sK3) != X1_53
% 39.25/5.50      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 39.25/5.50      | u1_struct_0(sK3) != X0_53
% 39.25/5.50      | sK4 != X2_53 ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_2453]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_5050,plain,
% 39.25/5.50      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),X0_53,X1_53)
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4)
% 39.25/5.50      | k4_tmap_1(sK2,sK3) != X0_53
% 39.25/5.50      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 39.25/5.50      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 39.25/5.50      | sK4 != X1_53 ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_2646]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_5051,plain,
% 39.25/5.50      ( k4_tmap_1(sK2,sK3) != X0_53
% 39.25/5.50      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 39.25/5.50      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 39.25/5.50      | sK4 != X1_53
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),X0_53,X1_53) != iProver_top
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) = iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_5050]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_5053,plain,
% 39.25/5.50      ( k4_tmap_1(sK2,sK3) != sK4
% 39.25/5.50      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 39.25/5.50      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 39.25/5.50      | sK4 != sK4
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k4_tmap_1(sK2,sK3),sK4) = iProver_top
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,sK4) != iProver_top ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_5051]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_6383,plain,
% 39.25/5.50      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_1652]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_8120,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3))
% 39.25/5.50      | v1_xboole_0(u1_struct_0(sK3))
% 39.25/5.50      | k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)) ),
% 39.25/5.50      inference(predicate_to_equality_rev,[status(thm)],[c_8118]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_5080,plain,
% 39.25/5.50      ( ~ r2_funct_2(X0_53,X1_53,X2_53,k4_tmap_1(X0_52,X1_52))
% 39.25/5.50      | ~ v1_funct_2(X2_53,X0_53,X1_53)
% 39.25/5.50      | ~ v1_funct_2(k4_tmap_1(X0_52,X1_52),X0_53,X1_53)
% 39.25/5.50      | ~ m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 39.25/5.50      | ~ m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 39.25/5.50      | ~ v1_funct_1(X2_53)
% 39.25/5.50      | ~ v1_funct_1(k4_tmap_1(X0_52,X1_52))
% 39.25/5.50      | k4_tmap_1(X0_52,X1_52) = X2_53 ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_1644]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_8260,plain,
% 39.25/5.50      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(X0_52,X1_52))
% 39.25/5.50      | ~ v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(sK3),u1_struct_0(sK2))
% 39.25/5.50      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
% 39.25/5.50      | ~ m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 39.25/5.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 39.25/5.50      | ~ v1_funct_1(k4_tmap_1(X0_52,X1_52))
% 39.25/5.50      | ~ v1_funct_1(sK4)
% 39.25/5.50      | k4_tmap_1(X0_52,X1_52) = sK4 ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_5080]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_8334,plain,
% 39.25/5.50      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3))
% 39.25/5.50      | ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
% 39.25/5.50      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
% 39.25/5.50      | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 39.25/5.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 39.25/5.50      | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
% 39.25/5.50      | ~ v1_funct_1(sK4)
% 39.25/5.50      | k4_tmap_1(sK2,sK3) = sK4 ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_8260]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_18,plain,
% 39.25/5.50      ( ~ m1_pre_topc(X0,X1)
% 39.25/5.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 39.25/5.50      | ~ l1_pre_topc(X1) ),
% 39.25/5.50      inference(cnf_transformation,[],[f81]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1632,plain,
% 39.25/5.50      ( ~ m1_pre_topc(X0_52,X1_52)
% 39.25/5.50      | m1_subset_1(u1_struct_0(X0_52),k1_zfmisc_1(u1_struct_0(X1_52)))
% 39.25/5.50      | ~ l1_pre_topc(X1_52) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_18]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_26945,plain,
% 39.25/5.50      ( ~ m1_pre_topc(sK3,sK3)
% 39.25/5.50      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 39.25/5.50      | ~ l1_pre_topc(sK3) ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_1632]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_11,plain,
% 39.25/5.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 39.25/5.50      | ~ m1_pre_topc(X3,X4)
% 39.25/5.50      | ~ m1_pre_topc(X3,X1)
% 39.25/5.50      | ~ m1_pre_topc(X1,X4)
% 39.25/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 39.25/5.50      | v2_struct_0(X4)
% 39.25/5.50      | v2_struct_0(X2)
% 39.25/5.50      | ~ l1_pre_topc(X4)
% 39.25/5.50      | ~ l1_pre_topc(X2)
% 39.25/5.50      | ~ v2_pre_topc(X4)
% 39.25/5.50      | ~ v2_pre_topc(X2)
% 39.25/5.50      | ~ v1_funct_1(X0)
% 39.25/5.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 39.25/5.50      inference(cnf_transformation,[],[f74]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1639,plain,
% 39.25/5.50      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 39.25/5.50      | ~ m1_pre_topc(X2_52,X0_52)
% 39.25/5.50      | ~ m1_pre_topc(X0_52,X3_52)
% 39.25/5.50      | ~ m1_pre_topc(X2_52,X3_52)
% 39.25/5.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 39.25/5.50      | v2_struct_0(X1_52)
% 39.25/5.50      | v2_struct_0(X3_52)
% 39.25/5.50      | ~ l1_pre_topc(X1_52)
% 39.25/5.50      | ~ l1_pre_topc(X3_52)
% 39.25/5.50      | ~ v2_pre_topc(X1_52)
% 39.25/5.50      | ~ v2_pre_topc(X3_52)
% 39.25/5.50      | ~ v1_funct_1(X0_53)
% 39.25/5.50      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_11]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2261,plain,
% 39.25/5.50      ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53)
% 39.25/5.50      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 39.25/5.50      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 39.25/5.50      | m1_pre_topc(X2_52,X3_52) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | v2_struct_0(X3_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | l1_pre_topc(X3_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X3_52) != iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1639]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4529,plain,
% 39.25/5.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK2,sK3,X0_52,sK4)
% 39.25/5.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,sK3) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,X1_52) != iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v1_funct_1(sK4) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_2278,c_2261]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4879,plain,
% 39.25/5.50      ( l1_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK2,sK3,X0_52,sK4)
% 39.25/5.50      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,sK3) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,X1_52) != iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | v2_pre_topc(X1_52) != iProver_top ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_4529,c_36,c_37,c_38,c_41,c_42,c_43,c_2542]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4880,plain,
% 39.25/5.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK2,sK3,X0_52,sK4)
% 39.25/5.50      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,sK3) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,X1_52) != iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X1_52) != iProver_top ),
% 39.25/5.50      inference(renaming,[status(thm)],[c_4879]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4885,plain,
% 39.25/5.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK2,sK2,sK3,sK3,sK4)
% 39.25/5.50      | m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,sK3) != iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_2281,c_4880]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2269,plain,
% 39.25/5.50      ( m1_pre_topc(X0_52,X0_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X0_52) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1631]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_10,plain,
% 39.25/5.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 39.25/5.50      | ~ m1_pre_topc(X3,X1)
% 39.25/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 39.25/5.50      | v2_struct_0(X1)
% 39.25/5.50      | v2_struct_0(X2)
% 39.25/5.50      | ~ l1_pre_topc(X1)
% 39.25/5.50      | ~ l1_pre_topc(X2)
% 39.25/5.50      | ~ v2_pre_topc(X1)
% 39.25/5.50      | ~ v2_pre_topc(X2)
% 39.25/5.50      | ~ v1_funct_1(X0)
% 39.25/5.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 39.25/5.50      inference(cnf_transformation,[],[f73]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1640,plain,
% 39.25/5.50      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 39.25/5.50      | ~ m1_pre_topc(X2_52,X0_52)
% 39.25/5.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 39.25/5.50      | v2_struct_0(X1_52)
% 39.25/5.50      | v2_struct_0(X0_52)
% 39.25/5.50      | ~ l1_pre_topc(X1_52)
% 39.25/5.50      | ~ l1_pre_topc(X0_52)
% 39.25/5.50      | ~ v2_pre_topc(X1_52)
% 39.25/5.50      | ~ v2_pre_topc(X0_52)
% 39.25/5.50      | ~ v1_funct_1(X0_53)
% 39.25/5.50      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_53,X2_52) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_10]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2260,plain,
% 39.25/5.50      ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_53,X2_52)
% 39.25/5.50      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 39.25/5.50      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 39.25/5.50      | v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X0_52) != iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X0_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1640]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4026,plain,
% 39.25/5.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK3,sK2,sK4,X0_52)
% 39.25/5.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,sK3) != iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | v2_struct_0(sK3) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | l1_pre_topc(sK3) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK3) != iProver_top
% 39.25/5.50      | v1_funct_1(sK4) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_2278,c_2260]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2469,plain,
% 39.25/5.50      ( m1_pre_topc(sK3,X0_52) != iProver_top
% 39.25/5.50      | l1_pre_topc(X0_52) != iProver_top
% 39.25/5.50      | l1_pre_topc(sK3) = iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_2468]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2471,plain,
% 39.25/5.50      ( m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | l1_pre_topc(sK3) = iProver_top ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_2469]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2792,plain,
% 39.25/5.50      ( m1_pre_topc(sK3,X0_52) != iProver_top
% 39.25/5.50      | l1_pre_topc(X0_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X0_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK3) = iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_2791]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2794,plain,
% 39.25/5.50      ( m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK3) = iProver_top ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_2792]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4092,plain,
% 39.25/5.50      ( m1_pre_topc(X0_52,sK3) != iProver_top
% 39.25/5.50      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK3,sK2,sK4,X0_52) ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_4026,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_2471,c_2794]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4093,plain,
% 39.25/5.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK3,sK2,sK4,X0_52)
% 39.25/5.50      | m1_pre_topc(X0_52,sK3) != iProver_top ),
% 39.25/5.50      inference(renaming,[status(thm)],[c_4092]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4098,plain,
% 39.25/5.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK3,sK2,sK4,sK3)
% 39.25/5.50      | l1_pre_topc(sK3) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_2269,c_4093]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4101,plain,
% 39.25/5.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK3,sK2,sK4,sK3) ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_4098,c_38,c_40,c_2471]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4887,plain,
% 39.25/5.50      ( k3_tmap_1(sK2,sK2,sK3,sK3,sK4) = k2_tmap_1(sK3,sK2,sK4,sK3)
% 39.25/5.50      | m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,sK3) != iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top ),
% 39.25/5.50      inference(light_normalisation,[status(thm)],[c_4885,c_4101]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_3079,plain,
% 39.25/5.50      ( m1_pre_topc(sK3,sK3) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK3) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_3078]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4921,plain,
% 39.25/5.50      ( k3_tmap_1(sK2,sK2,sK3,sK3,sK4) = k2_tmap_1(sK3,sK2,sK4,sK3) ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_4887,c_36,c_37,c_38,c_40,c_2471,c_3079]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_12,plain,
% 39.25/5.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 39.25/5.50      | ~ m1_pre_topc(X3,X4)
% 39.25/5.50      | ~ m1_pre_topc(X1,X4)
% 39.25/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 39.25/5.50      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 39.25/5.50      | v2_struct_0(X4)
% 39.25/5.50      | v2_struct_0(X2)
% 39.25/5.50      | ~ l1_pre_topc(X4)
% 39.25/5.50      | ~ l1_pre_topc(X2)
% 39.25/5.50      | ~ v2_pre_topc(X4)
% 39.25/5.50      | ~ v2_pre_topc(X2)
% 39.25/5.50      | ~ v1_funct_1(X0) ),
% 39.25/5.50      inference(cnf_transformation,[],[f77]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1638,plain,
% 39.25/5.50      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 39.25/5.50      | ~ m1_pre_topc(X0_52,X2_52)
% 39.25/5.50      | ~ m1_pre_topc(X3_52,X2_52)
% 39.25/5.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 39.25/5.50      | m1_subset_1(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
% 39.25/5.50      | v2_struct_0(X1_52)
% 39.25/5.50      | v2_struct_0(X2_52)
% 39.25/5.50      | ~ l1_pre_topc(X1_52)
% 39.25/5.50      | ~ l1_pre_topc(X2_52)
% 39.25/5.50      | ~ v2_pre_topc(X1_52)
% 39.25/5.50      | ~ v2_pre_topc(X2_52)
% 39.25/5.50      | ~ v1_funct_1(X0_53) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_12]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2262,plain,
% 39.25/5.50      ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 39.25/5.50      | m1_pre_topc(X3_52,X2_52) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 39.25/5.50      | m1_subset_1(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52)))) = iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | v2_struct_0(X2_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | l1_pre_topc(X2_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X2_52) != iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1638]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4924,plain,
% 39.25/5.50      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | m1_subset_1(k2_tmap_1(sK3,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top
% 39.25/5.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v1_funct_1(sK4) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_4921,c_2262]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_43,plain,
% 39.25/5.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_5425,plain,
% 39.25/5.50      ( m1_subset_1(k2_tmap_1(sK3,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_4924,c_36,c_37,c_38,c_40,c_41,c_42,c_43]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_3732,plain,
% 39.25/5.50      ( sK4 = X0_53
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),X0_53,sK4) != iProver_top
% 39.25/5.50      | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top
% 39.25/5.50      | v1_funct_1(sK4) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_2278,c_2256]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_3735,plain,
% 39.25/5.50      ( v1_funct_1(X0_53) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | sK4 = X0_53
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),X0_53,sK4) != iProver_top
% 39.25/5.50      | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_3732,c_41,c_42]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_3736,plain,
% 39.25/5.50      ( sK4 = X0_53
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),X0_53,sK4) != iProver_top
% 39.25/5.50      | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top ),
% 39.25/5.50      inference(renaming,[status(thm)],[c_3735]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_5440,plain,
% 39.25/5.50      ( k2_tmap_1(sK3,sK2,sK4,sK3) = sK4
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK3,sK2,sK4,sK3),sK4) != iProver_top
% 39.25/5.50      | v1_funct_2(k2_tmap_1(sK3,sK2,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | v1_funct_1(k2_tmap_1(sK3,sK2,sK4,sK3)) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_5425,c_3736]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_23,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
% 39.25/5.50      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 39.25/5.50      | ~ m1_pre_topc(X0,X3)
% 39.25/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 39.25/5.50      | v2_struct_0(X3)
% 39.25/5.50      | v2_struct_0(X1)
% 39.25/5.50      | v2_struct_0(X0)
% 39.25/5.50      | ~ l1_pre_topc(X3)
% 39.25/5.50      | ~ l1_pre_topc(X1)
% 39.25/5.50      | ~ v2_pre_topc(X3)
% 39.25/5.50      | ~ v2_pre_topc(X1)
% 39.25/5.50      | ~ v1_funct_1(X2) ),
% 39.25/5.50      inference(cnf_transformation,[],[f86]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1627,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,k3_tmap_1(X2_52,X1_52,X0_52,X0_52,X0_53))
% 39.25/5.50      | ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 39.25/5.50      | ~ m1_pre_topc(X0_52,X2_52)
% 39.25/5.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 39.25/5.50      | v2_struct_0(X1_52)
% 39.25/5.50      | v2_struct_0(X0_52)
% 39.25/5.50      | v2_struct_0(X2_52)
% 39.25/5.50      | ~ l1_pre_topc(X1_52)
% 39.25/5.50      | ~ l1_pre_topc(X2_52)
% 39.25/5.50      | ~ v2_pre_topc(X1_52)
% 39.25/5.50      | ~ v2_pre_topc(X2_52)
% 39.25/5.50      | ~ v1_funct_1(X0_53) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_23]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2273,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,k3_tmap_1(X2_52,X1_52,X0_52,X0_52,X0_53)) = iProver_top
% 39.25/5.50      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 39.25/5.50      | v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | v2_struct_0(X2_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | l1_pre_topc(X2_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X2_52) != iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1627]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4923,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k2_tmap_1(sK3,sK2,sK4,sK3)) = iProver_top
% 39.25/5.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | v2_struct_0(sK3) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v1_funct_1(sK4) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_4921,c_2273]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_13,plain,
% 39.25/5.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 39.25/5.50      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 39.25/5.50      | ~ m1_pre_topc(X4,X3)
% 39.25/5.50      | ~ m1_pre_topc(X1,X3)
% 39.25/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 39.25/5.50      | v2_struct_0(X3)
% 39.25/5.50      | v2_struct_0(X2)
% 39.25/5.50      | ~ l1_pre_topc(X3)
% 39.25/5.50      | ~ l1_pre_topc(X2)
% 39.25/5.50      | ~ v2_pre_topc(X3)
% 39.25/5.50      | ~ v2_pre_topc(X2)
% 39.25/5.50      | ~ v1_funct_1(X0) ),
% 39.25/5.50      inference(cnf_transformation,[],[f76]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1637,plain,
% 39.25/5.50      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 39.25/5.50      | v1_funct_2(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53),u1_struct_0(X3_52),u1_struct_0(X1_52))
% 39.25/5.50      | ~ m1_pre_topc(X0_52,X2_52)
% 39.25/5.50      | ~ m1_pre_topc(X3_52,X2_52)
% 39.25/5.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 39.25/5.50      | v2_struct_0(X1_52)
% 39.25/5.50      | v2_struct_0(X2_52)
% 39.25/5.50      | ~ l1_pre_topc(X1_52)
% 39.25/5.50      | ~ l1_pre_topc(X2_52)
% 39.25/5.50      | ~ v2_pre_topc(X1_52)
% 39.25/5.50      | ~ v2_pre_topc(X2_52)
% 39.25/5.50      | ~ v1_funct_1(X0_53) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_13]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2263,plain,
% 39.25/5.50      ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 39.25/5.50      | v1_funct_2(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53),u1_struct_0(X3_52),u1_struct_0(X1_52)) = iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 39.25/5.50      | m1_pre_topc(X3_52,X2_52) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | v2_struct_0(X2_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | l1_pre_topc(X2_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X2_52) != iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1637]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4925,plain,
% 39.25/5.50      ( v1_funct_2(k2_tmap_1(sK3,sK2,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
% 39.25/5.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v1_funct_1(sK4) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_4921,c_2263]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_14,plain,
% 39.25/5.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 39.25/5.50      | ~ m1_pre_topc(X3,X4)
% 39.25/5.50      | ~ m1_pre_topc(X1,X4)
% 39.25/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 39.25/5.50      | v2_struct_0(X4)
% 39.25/5.50      | v2_struct_0(X2)
% 39.25/5.50      | ~ l1_pre_topc(X4)
% 39.25/5.50      | ~ l1_pre_topc(X2)
% 39.25/5.50      | ~ v2_pre_topc(X4)
% 39.25/5.50      | ~ v2_pre_topc(X2)
% 39.25/5.50      | ~ v1_funct_1(X0)
% 39.25/5.50      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 39.25/5.50      inference(cnf_transformation,[],[f75]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1636,plain,
% 39.25/5.50      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 39.25/5.50      | ~ m1_pre_topc(X0_52,X2_52)
% 39.25/5.50      | ~ m1_pre_topc(X3_52,X2_52)
% 39.25/5.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 39.25/5.50      | v2_struct_0(X1_52)
% 39.25/5.50      | v2_struct_0(X2_52)
% 39.25/5.50      | ~ l1_pre_topc(X1_52)
% 39.25/5.50      | ~ l1_pre_topc(X2_52)
% 39.25/5.50      | ~ v2_pre_topc(X1_52)
% 39.25/5.50      | ~ v2_pre_topc(X2_52)
% 39.25/5.50      | ~ v1_funct_1(X0_53)
% 39.25/5.50      | v1_funct_1(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53)) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_14]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2264,plain,
% 39.25/5.50      ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 39.25/5.50      | m1_pre_topc(X3_52,X2_52) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | v2_struct_0(X2_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | l1_pre_topc(X2_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X2_52) != iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top
% 39.25/5.50      | v1_funct_1(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53)) = iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1636]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4722,plain,
% 39.25/5.50      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,X1_52) != iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v1_funct_1(k3_tmap_1(X1_52,sK2,sK3,X0_52,sK4)) = iProver_top
% 39.25/5.50      | v1_funct_1(sK4) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_2278,c_2264]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4872,plain,
% 39.25/5.50      ( v1_funct_1(k3_tmap_1(X1_52,sK2,sK3,X0_52,sK4)) = iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,X1_52) != iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | v2_pre_topc(X1_52) != iProver_top ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_4722,c_36,c_37,c_38,c_41,c_42]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4873,plain,
% 39.25/5.50      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,X1_52) != iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | v1_funct_1(k3_tmap_1(X1_52,sK2,sK3,X0_52,sK4)) = iProver_top ),
% 39.25/5.50      inference(renaming,[status(thm)],[c_4872]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4926,plain,
% 39.25/5.50      ( m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v1_funct_1(k2_tmap_1(sK3,sK2,sK4,sK3)) = iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_4921,c_4873]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_5436,plain,
% 39.25/5.50      ( k2_tmap_1(sK3,sK2,sK4,sK3) = X0_53
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),X0_53,k2_tmap_1(sK3,sK2,sK4,sK3)) != iProver_top
% 39.25/5.50      | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | v1_funct_2(k2_tmap_1(sK3,sK2,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top
% 39.25/5.50      | v1_funct_1(k2_tmap_1(sK3,sK2,sK4,sK3)) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_5425,c_2256]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_5459,plain,
% 39.25/5.50      ( k2_tmap_1(sK3,sK2,sK4,sK3) = sK4
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k2_tmap_1(sK3,sK2,sK4,sK3)) != iProver_top
% 39.25/5.50      | v1_funct_2(k2_tmap_1(sK3,sK2,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | v1_funct_1(k2_tmap_1(sK3,sK2,sK4,sK3)) != iProver_top
% 39.25/5.50      | v1_funct_1(sK4) != iProver_top ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_5436]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_5470,plain,
% 39.25/5.50      ( k2_tmap_1(sK3,sK2,sK4,sK3) = sK4 ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_5440,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_4923,
% 39.25/5.50                 c_4925,c_4926,c_5459]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_21,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 39.25/5.50      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 39.25/5.50      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 39.25/5.50      | ~ m1_pre_topc(X0,X2)
% 39.25/5.50      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 39.25/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 39.25/5.50      | r2_hidden(sK1(X1,X2,X0,X3,X4),u1_struct_0(X0))
% 39.25/5.50      | v2_struct_0(X1)
% 39.25/5.50      | v2_struct_0(X2)
% 39.25/5.50      | v2_struct_0(X0)
% 39.25/5.50      | ~ l1_pre_topc(X1)
% 39.25/5.50      | ~ l1_pre_topc(X2)
% 39.25/5.50      | ~ v2_pre_topc(X1)
% 39.25/5.50      | ~ v2_pre_topc(X2)
% 39.25/5.50      | ~ v1_funct_1(X3)
% 39.25/5.50      | ~ v1_funct_1(X4) ),
% 39.25/5.50      inference(cnf_transformation,[],[f84]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1629,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_53,X0_52),X1_53)
% 39.25/5.50      | ~ v1_funct_2(X1_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 39.25/5.50      | ~ v1_funct_2(X0_53,u1_struct_0(X2_52),u1_struct_0(X1_52))
% 39.25/5.50      | ~ m1_pre_topc(X0_52,X2_52)
% 39.25/5.50      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 39.25/5.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 39.25/5.50      | r2_hidden(sK1(X1_52,X2_52,X0_52,X0_53,X1_53),u1_struct_0(X0_52))
% 39.25/5.50      | v2_struct_0(X1_52)
% 39.25/5.50      | v2_struct_0(X0_52)
% 39.25/5.50      | v2_struct_0(X2_52)
% 39.25/5.50      | ~ l1_pre_topc(X1_52)
% 39.25/5.50      | ~ l1_pre_topc(X2_52)
% 39.25/5.50      | ~ v2_pre_topc(X1_52)
% 39.25/5.50      | ~ v2_pre_topc(X2_52)
% 39.25/5.50      | ~ v1_funct_1(X0_53)
% 39.25/5.50      | ~ v1_funct_1(X1_53) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_21]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2271,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_53,X0_52),X1_53) = iProver_top
% 39.25/5.50      | v1_funct_2(X1_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 39.25/5.50      | v1_funct_2(X0_53,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
% 39.25/5.50      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 39.25/5.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
% 39.25/5.50      | r2_hidden(sK1(X1_52,X2_52,X0_52,X0_53,X1_53),u1_struct_0(X0_52)) = iProver_top
% 39.25/5.50      | v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | v2_struct_0(X2_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | l1_pre_topc(X2_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X2_52) != iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top
% 39.25/5.50      | v1_funct_1(X1_53) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1629]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_7495,plain,
% 39.25/5.50      ( k2_tmap_1(X0_52,X1_52,X0_53,X2_52) = k4_tmap_1(X1_52,X2_52)
% 39.25/5.50      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 39.25/5.50      | v1_funct_2(k2_tmap_1(X0_52,X1_52,X0_53,X2_52),u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
% 39.25/5.50      | v1_funct_2(k4_tmap_1(X1_52,X2_52),u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
% 39.25/5.50      | m1_pre_topc(X2_52,X1_52) != iProver_top
% 39.25/5.50      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 39.25/5.50      | m1_subset_1(k2_tmap_1(X0_52,X1_52,X0_53,X2_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
% 39.25/5.50      | m1_subset_1(k4_tmap_1(X1_52,X2_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
% 39.25/5.50      | r2_hidden(sK1(X1_52,X0_52,X2_52,X0_53,k4_tmap_1(X1_52,X2_52)),u1_struct_0(X2_52)) = iProver_top
% 39.25/5.50      | v2_struct_0(X1_52) = iProver_top
% 39.25/5.50      | v2_struct_0(X2_52) = iProver_top
% 39.25/5.50      | v2_struct_0(X0_52) = iProver_top
% 39.25/5.50      | l1_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | l1_pre_topc(X0_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X1_52) != iProver_top
% 39.25/5.50      | v2_pre_topc(X0_52) != iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top
% 39.25/5.50      | v1_funct_1(k2_tmap_1(X0_52,X1_52,X0_53,X2_52)) != iProver_top
% 39.25/5.50      | v1_funct_1(k4_tmap_1(X1_52,X2_52)) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_2271,c_7489]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_34639,plain,
% 39.25/5.50      ( k2_tmap_1(sK3,sK2,sK4,sK3) = k4_tmap_1(sK2,sK3)
% 39.25/5.50      | v1_funct_2(k2_tmap_1(sK3,sK2,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,sK3) != iProver_top
% 39.25/5.50      | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | r2_hidden(sK1(sK2,sK3,sK3,sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | v2_struct_0(sK3) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | l1_pre_topc(sK3) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK3) != iProver_top
% 39.25/5.50      | v1_funct_1(k2_tmap_1(sK3,sK2,sK4,sK3)) != iProver_top
% 39.25/5.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 39.25/5.50      | v1_funct_1(sK4) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_5470,c_7495]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_34640,plain,
% 39.25/5.50      ( k4_tmap_1(sK2,sK3) = sK4
% 39.25/5.50      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,sK3) != iProver_top
% 39.25/5.50      | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | r2_hidden(sK1(sK2,sK3,sK3,sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) = iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | v2_struct_0(sK3) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | l1_pre_topc(sK3) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK3) != iProver_top
% 39.25/5.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 39.25/5.50      | v1_funct_1(sK4) != iProver_top ),
% 39.25/5.50      inference(light_normalisation,[status(thm)],[c_34639,c_5470]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_34645,plain,
% 39.25/5.50      ( ~ v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))
% 39.25/5.50      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
% 39.25/5.50      | ~ m1_pre_topc(sK3,sK2)
% 39.25/5.50      | ~ m1_pre_topc(sK3,sK3)
% 39.25/5.50      | ~ m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 39.25/5.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 39.25/5.50      | r2_hidden(sK1(sK2,sK3,sK3,sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3))
% 39.25/5.50      | v2_struct_0(sK2)
% 39.25/5.50      | v2_struct_0(sK3)
% 39.25/5.50      | ~ l1_pre_topc(sK2)
% 39.25/5.50      | ~ l1_pre_topc(sK3)
% 39.25/5.50      | ~ v2_pre_topc(sK2)
% 39.25/5.50      | ~ v2_pre_topc(sK3)
% 39.25/5.50      | ~ v1_funct_1(k4_tmap_1(sK2,sK3))
% 39.25/5.50      | ~ v1_funct_1(sK4)
% 39.25/5.50      | k4_tmap_1(sK2,sK3) = sK4 ),
% 39.25/5.50      inference(predicate_to_equality_rev,[status(thm)],[c_34640]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1,plain,
% 39.25/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.25/5.50      | ~ r2_hidden(X2,X0)
% 39.25/5.50      | ~ v1_xboole_0(X1) ),
% 39.25/5.50      inference(cnf_transformation,[],[f64]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1649,plain,
% 39.25/5.50      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 39.25/5.50      | ~ r2_hidden(X2_53,X0_53)
% 39.25/5.50      | ~ v1_xboole_0(X1_53) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_1]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_8961,plain,
% 39.25/5.50      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0_53))
% 39.25/5.50      | ~ r2_hidden(sK1(sK2,sK3,sK3,sK4,X1_53),u1_struct_0(sK3))
% 39.25/5.50      | ~ v1_xboole_0(X0_53) ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_1649]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_17736,plain,
% 39.25/5.50      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 39.25/5.50      | ~ r2_hidden(sK1(sK2,sK3,sK3,sK4,X0_53),u1_struct_0(sK3))
% 39.25/5.50      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_8961]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_43563,plain,
% 39.25/5.50      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 39.25/5.50      | ~ r2_hidden(sK1(sK2,sK3,sK3,sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3))
% 39.25/5.50      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 39.25/5.50      inference(instantiation,[status(thm)],[c_17736]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_56631,plain,
% 39.25/5.50      ( k1_funct_1(k4_tmap_1(sK2,sK3),sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)) ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_8122,c_35,c_34,c_33,c_32,c_31,c_30,c_41,c_29,c_42,
% 39.25/5.50                 c_28,c_47,c_1675,c_2470,c_2596,c_2757,c_2793,c_3078,
% 39.25/5.50                 c_3139,c_3238,c_3279,c_5053,c_6383,c_8120,c_8334,
% 39.25/5.50                 c_26945,c_34645,c_43563]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2,plain,
% 39.25/5.50      ( r2_funct_2(X0,X1,X2,X3)
% 39.25/5.50      | ~ v1_funct_2(X3,X0,X1)
% 39.25/5.50      | ~ v1_funct_2(X2,X0,X1)
% 39.25/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.25/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.25/5.50      | ~ v1_funct_1(X3)
% 39.25/5.50      | ~ v1_funct_1(X2)
% 39.25/5.50      | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
% 39.25/5.50      inference(cnf_transformation,[],[f67]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1648,plain,
% 39.25/5.50      ( r2_funct_2(X0_53,X1_53,X2_53,X3_53)
% 39.25/5.50      | ~ v1_funct_2(X3_53,X0_53,X1_53)
% 39.25/5.50      | ~ v1_funct_2(X2_53,X0_53,X1_53)
% 39.25/5.50      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 39.25/5.50      | ~ m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 39.25/5.50      | ~ v1_funct_1(X2_53)
% 39.25/5.50      | ~ v1_funct_1(X3_53)
% 39.25/5.50      | k1_funct_1(X3_53,sK0(X0_53,X2_53,X3_53)) != k1_funct_1(X2_53,sK0(X0_53,X2_53,X3_53)) ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_2]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2252,plain,
% 39.25/5.50      ( k1_funct_1(X0_53,sK0(X1_53,X2_53,X0_53)) != k1_funct_1(X2_53,sK0(X1_53,X2_53,X0_53))
% 39.25/5.50      | r2_funct_2(X1_53,X3_53,X2_53,X0_53) = iProver_top
% 39.25/5.50      | v1_funct_2(X2_53,X1_53,X3_53) != iProver_top
% 39.25/5.50      | v1_funct_2(X0_53,X1_53,X3_53) != iProver_top
% 39.25/5.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 39.25/5.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 39.25/5.50      | v1_funct_1(X2_53) != iProver_top
% 39.25/5.50      | v1_funct_1(X0_53) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1648]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_56633,plain,
% 39.25/5.50      ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) != sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),X0_53,sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),X0_53) != iProver_top
% 39.25/5.50      | v1_funct_2(sK4,u1_struct_0(sK3),X0_53) != iProver_top
% 39.25/5.50      | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0_53))) != iProver_top
% 39.25/5.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0_53))) != iProver_top
% 39.25/5.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 39.25/5.50      | v1_funct_1(sK4) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_56631,c_2252]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_27,negated_conjecture,
% 39.25/5.50      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 39.25/5.50      | ~ r2_hidden(X0,u1_struct_0(sK3))
% 39.25/5.50      | k1_funct_1(sK4,X0) = X0 ),
% 39.25/5.50      inference(cnf_transformation,[],[f97]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_1623,negated_conjecture,
% 39.25/5.50      ( ~ m1_subset_1(X0_53,u1_struct_0(sK2))
% 39.25/5.50      | ~ r2_hidden(X0_53,u1_struct_0(sK3))
% 39.25/5.50      | k1_funct_1(sK4,X0_53) = X0_53 ),
% 39.25/5.50      inference(subtyping,[status(esa)],[c_27]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_2277,plain,
% 39.25/5.50      ( k1_funct_1(sK4,X0_53) = X0_53
% 39.25/5.50      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | r2_hidden(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_1623]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4286,plain,
% 39.25/5.50      ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | r2_hidden(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) != iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_4281,c_2277]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4301,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | k1_funct_1(sK4,sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
% 39.25/5.50      | r2_hidden(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) != iProver_top ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_4286,c_36,c_38,c_40]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4302,plain,
% 39.25/5.50      ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | r2_hidden(sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)),u1_struct_0(sK3)) != iProver_top ),
% 39.25/5.50      inference(renaming,[status(thm)],[c_4301]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4305,plain,
% 39.25/5.50      ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_4126,c_4302]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_4306,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3))
% 39.25/5.50      | v1_xboole_0(u1_struct_0(sK3))
% 39.25/5.50      | k1_funct_1(sK4,sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3))) = sK0(u1_struct_0(sK3),sK4,k4_tmap_1(sK2,sK3)) ),
% 39.25/5.50      inference(predicate_to_equality_rev,[status(thm)],[c_4305]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_56944,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),X0_53,sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),X0_53) != iProver_top
% 39.25/5.50      | v1_funct_2(sK4,u1_struct_0(sK3),X0_53) != iProver_top
% 39.25/5.50      | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0_53))) != iProver_top
% 39.25/5.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0_53))) != iProver_top ),
% 39.25/5.50      inference(global_propositional_subsumption,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_56633,c_35,c_36,c_34,c_37,c_33,c_38,c_32,c_31,c_40,
% 39.25/5.50                 c_30,c_41,c_29,c_42,c_28,c_47,c_1675,c_2470,c_2596,
% 39.25/5.50                 c_2597,c_2757,c_2793,c_3078,c_3139,c_3238,c_3279,c_4306,
% 39.25/5.50                 c_5053,c_6383,c_8334,c_26945,c_34645,c_43563]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_56950,plain,
% 39.25/5.50      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) = iProver_top
% 39.25/5.50      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top ),
% 39.25/5.50      inference(superposition,[status(thm)],[c_2265,c_56944]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_8335,plain,
% 39.25/5.50      ( k4_tmap_1(sK2,sK3) = sK4
% 39.25/5.50      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK4,k4_tmap_1(sK2,sK3)) != iProver_top
% 39.25/5.50      | v1_funct_2(k4_tmap_1(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 39.25/5.50      | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 39.25/5.50      | v1_funct_1(k4_tmap_1(sK2,sK3)) != iProver_top
% 39.25/5.50      | v1_funct_1(sK4) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_8334]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(c_3140,plain,
% 39.25/5.50      ( m1_pre_topc(sK3,sK2) != iProver_top
% 39.25/5.50      | m1_subset_1(k4_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top
% 39.25/5.50      | v2_struct_0(sK2) = iProver_top
% 39.25/5.50      | l1_pre_topc(sK2) != iProver_top
% 39.25/5.50      | v2_pre_topc(sK2) != iProver_top ),
% 39.25/5.50      inference(predicate_to_equality,[status(thm)],[c_3139]) ).
% 39.25/5.50  
% 39.25/5.50  cnf(contradiction,plain,
% 39.25/5.50      ( $false ),
% 39.25/5.50      inference(minisat,
% 39.25/5.50                [status(thm)],
% 39.25/5.50                [c_56950,c_8335,c_6383,c_5053,c_3279,c_3238,c_3140,
% 39.25/5.50                 c_2758,c_2597,c_1675,c_47,c_43,c_42,c_41,c_40,c_38,c_37,
% 39.25/5.50                 c_36]) ).
% 39.25/5.50  
% 39.25/5.50  
% 39.25/5.50  % SZS output end CNFRefutation for theBenchmark.p
% 39.25/5.50  
% 39.25/5.50  ------                               Statistics
% 39.25/5.50  
% 39.25/5.50  ------ General
% 39.25/5.50  
% 39.25/5.50  abstr_ref_over_cycles:                  0
% 39.25/5.50  abstr_ref_under_cycles:                 0
% 39.25/5.50  gc_basic_clause_elim:                   0
% 39.25/5.50  forced_gc_time:                         0
% 39.25/5.50  parsing_time:                           0.012
% 39.25/5.50  unif_index_cands_time:                  0.
% 39.25/5.50  unif_index_add_time:                    0.
% 39.25/5.50  orderings_time:                         0.
% 39.25/5.50  out_proof_time:                         0.032
% 39.25/5.50  total_time:                             4.635
% 39.25/5.50  num_of_symbols:                         57
% 39.25/5.50  num_of_terms:                           104448
% 39.25/5.50  
% 39.25/5.50  ------ Preprocessing
% 39.25/5.50  
% 39.25/5.50  num_of_splits:                          0
% 39.25/5.50  num_of_split_atoms:                     0
% 39.25/5.50  num_of_reused_defs:                     0
% 39.25/5.50  num_eq_ax_congr_red:                    48
% 39.25/5.50  num_of_sem_filtered_clauses:            1
% 39.25/5.50  num_of_subtypes:                        2
% 39.25/5.50  monotx_restored_types:                  1
% 39.25/5.50  sat_num_of_epr_types:                   0
% 39.25/5.50  sat_num_of_non_cyclic_types:            0
% 39.25/5.50  sat_guarded_non_collapsed_types:        1
% 39.25/5.50  num_pure_diseq_elim:                    0
% 39.25/5.50  simp_replaced_by:                       0
% 39.25/5.50  res_preprocessed:                       133
% 39.25/5.50  prep_upred:                             0
% 39.25/5.50  prep_unflattend:                        65
% 39.25/5.50  smt_new_axioms:                         0
% 39.25/5.50  pred_elim_cands:                        10
% 39.25/5.50  pred_elim:                              0
% 39.25/5.50  pred_elim_cl:                           0
% 39.25/5.50  pred_elim_cycles:                       3
% 39.25/5.50  merged_defs:                            0
% 39.25/5.50  merged_defs_ncl:                        0
% 39.25/5.50  bin_hyper_res:                          0
% 39.25/5.50  prep_cycles:                            3
% 39.25/5.50  pred_elim_time:                         0.053
% 39.25/5.50  splitting_time:                         0.
% 39.25/5.50  sem_filter_time:                        0.
% 39.25/5.50  monotx_time:                            0.001
% 39.25/5.50  subtype_inf_time:                       0.003
% 39.25/5.50  
% 39.25/5.50  ------ Problem properties
% 39.25/5.50  
% 39.25/5.50  clauses:                                36
% 39.25/5.50  conjectures:                            10
% 39.25/5.50  epr:                                    11
% 39.25/5.50  horn:                                   20
% 39.25/5.50  ground:                                 9
% 39.25/5.50  unary:                                  9
% 39.25/5.50  binary:                                 1
% 39.25/5.50  lits:                                   221
% 39.25/5.50  lits_eq:                                8
% 39.25/5.50  fd_pure:                                0
% 39.25/5.50  fd_pseudo:                              0
% 39.25/5.50  fd_cond:                                0
% 39.25/5.50  fd_pseudo_cond:                         1
% 39.25/5.50  ac_symbols:                             0
% 39.25/5.50  
% 39.25/5.50  ------ Propositional Solver
% 39.25/5.50  
% 39.25/5.50  prop_solver_calls:                      32
% 39.25/5.50  prop_fast_solver_calls:                 8403
% 39.25/5.50  smt_solver_calls:                       0
% 39.25/5.50  smt_fast_solver_calls:                  0
% 39.25/5.50  prop_num_of_clauses:                    25845
% 39.25/5.50  prop_preprocess_simplified:             58175
% 39.25/5.50  prop_fo_subsumed:                       1364
% 39.25/5.50  prop_solver_time:                       0.
% 39.25/5.50  smt_solver_time:                        0.
% 39.25/5.50  smt_fast_solver_time:                   0.
% 39.25/5.50  prop_fast_solver_time:                  0.
% 39.25/5.50  prop_unsat_core_time:                   0.005
% 39.25/5.50  
% 39.25/5.50  ------ QBF
% 39.25/5.50  
% 39.25/5.50  qbf_q_res:                              0
% 39.25/5.50  qbf_num_tautologies:                    0
% 39.25/5.50  qbf_prep_cycles:                        0
% 39.25/5.50  
% 39.25/5.50  ------ BMC1
% 39.25/5.50  
% 39.25/5.50  bmc1_current_bound:                     -1
% 39.25/5.50  bmc1_last_solved_bound:                 -1
% 39.25/5.50  bmc1_unsat_core_size:                   -1
% 39.25/5.50  bmc1_unsat_core_parents_size:           -1
% 39.25/5.50  bmc1_merge_next_fun:                    0
% 39.25/5.50  bmc1_unsat_core_clauses_time:           0.
% 39.25/5.50  
% 39.25/5.50  ------ Instantiation
% 39.25/5.50  
% 39.25/5.50  inst_num_of_clauses:                    7378
% 39.25/5.50  inst_num_in_passive:                    1902
% 39.25/5.50  inst_num_in_active:                     2426
% 39.25/5.50  inst_num_in_unprocessed:                3051
% 39.25/5.50  inst_num_of_loops:                      2880
% 39.25/5.50  inst_num_of_learning_restarts:          0
% 39.25/5.50  inst_num_moves_active_passive:          450
% 39.25/5.50  inst_lit_activity:                      0
% 39.25/5.50  inst_lit_activity_moves:                4
% 39.25/5.50  inst_num_tautologies:                   0
% 39.25/5.50  inst_num_prop_implied:                  0
% 39.25/5.50  inst_num_existing_simplified:           0
% 39.25/5.50  inst_num_eq_res_simplified:             0
% 39.25/5.50  inst_num_child_elim:                    0
% 39.25/5.50  inst_num_of_dismatching_blockings:      5805
% 39.25/5.50  inst_num_of_non_proper_insts:           7249
% 39.25/5.50  inst_num_of_duplicates:                 0
% 39.25/5.50  inst_inst_num_from_inst_to_res:         0
% 39.25/5.50  inst_dismatching_checking_time:         0.
% 39.25/5.50  
% 39.25/5.50  ------ Resolution
% 39.25/5.50  
% 39.25/5.50  res_num_of_clauses:                     0
% 39.25/5.50  res_num_in_passive:                     0
% 39.25/5.50  res_num_in_active:                      0
% 39.25/5.50  res_num_of_loops:                       136
% 39.25/5.50  res_forward_subset_subsumed:            82
% 39.25/5.50  res_backward_subset_subsumed:           2
% 39.25/5.50  res_forward_subsumed:                   0
% 39.25/5.50  res_backward_subsumed:                  0
% 39.25/5.50  res_forward_subsumption_resolution:     0
% 39.25/5.50  res_backward_subsumption_resolution:    0
% 39.25/5.50  res_clause_to_clause_subsumption:       9905
% 39.25/5.50  res_orphan_elimination:                 0
% 39.25/5.50  res_tautology_del:                      199
% 39.25/5.50  res_num_eq_res_simplified:              0
% 39.25/5.50  res_num_sel_changes:                    0
% 39.25/5.50  res_moves_from_active_to_pass:          0
% 39.25/5.50  
% 39.25/5.50  ------ Superposition
% 39.25/5.50  
% 39.25/5.50  sup_time_total:                         0.
% 39.25/5.50  sup_time_generating:                    0.
% 39.25/5.50  sup_time_sim_full:                      0.
% 39.25/5.50  sup_time_sim_immed:                     0.
% 39.25/5.50  
% 39.25/5.50  sup_num_of_clauses:                     1223
% 39.25/5.50  sup_num_in_active:                      492
% 39.25/5.50  sup_num_in_passive:                     731
% 39.25/5.50  sup_num_of_loops:                       575
% 39.25/5.50  sup_fw_superposition:                   1363
% 39.25/5.50  sup_bw_superposition:                   797
% 39.25/5.50  sup_immediate_simplified:               813
% 39.25/5.50  sup_given_eliminated:                   4
% 39.25/5.50  comparisons_done:                       0
% 39.25/5.50  comparisons_avoided:                    450
% 39.25/5.50  
% 39.25/5.50  ------ Simplifications
% 39.25/5.50  
% 39.25/5.50  
% 39.25/5.50  sim_fw_subset_subsumed:                 148
% 39.25/5.50  sim_bw_subset_subsumed:                 169
% 39.25/5.50  sim_fw_subsumed:                        294
% 39.25/5.50  sim_bw_subsumed:                        175
% 39.25/5.50  sim_fw_subsumption_res:                 0
% 39.25/5.50  sim_bw_subsumption_res:                 0
% 39.25/5.50  sim_tautology_del:                      11
% 39.25/5.50  sim_eq_tautology_del:                   44
% 39.25/5.50  sim_eq_res_simp:                        0
% 39.25/5.50  sim_fw_demodulated:                     51
% 39.25/5.50  sim_bw_demodulated:                     32
% 39.25/5.50  sim_light_normalised:                   218
% 39.25/5.50  sim_joinable_taut:                      0
% 39.25/5.50  sim_joinable_simp:                      0
% 39.25/5.50  sim_ac_normalised:                      0
% 39.25/5.50  sim_smt_subsumption:                    0
% 39.25/5.50  
%------------------------------------------------------------------------------
