%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1263+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:16 EST 2020

% Result     : Timeout 59.74s
% Output     : None 
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_31661)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r1_xboole_0(X1,X2)
                    & v3_pre_topc(X2,X0)
                    & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( r1_xboole_0(X1,X2)
                      & v3_pre_topc(X2,X0)
                      & k1_xboole_0 != X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_1(X1,X0)
          <~> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_1(X1,X0)
          <~> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,X0)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v1_tops_1(X1,X0) )
          & ( ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v1_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,X0)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v1_tops_1(X1,X0) )
          & ( ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v1_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,X0)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v1_tops_1(X1,X0) )
          & ( ! [X3] :
                ( ~ r1_xboole_0(X1,X3)
                | ~ v3_pre_topc(X3,X0)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v1_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f61])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_xboole_0(X1,X2)
          & v3_pre_topc(X2,X0)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK5)
        & v3_pre_topc(sK5,X0)
        & k1_xboole_0 != sK5
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,X0)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v1_tops_1(X1,X0) )
          & ( ! [X3] :
                ( ~ r1_xboole_0(X1,X3)
                | ~ v3_pre_topc(X3,X0)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v1_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ? [X2] :
              ( r1_xboole_0(sK4,X2)
              & v3_pre_topc(X2,X0)
              & k1_xboole_0 != X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(sK4,X0) )
        & ( ! [X3] :
              ( ~ r1_xboole_0(sK4,X3)
              | ~ v3_pre_topc(X3,X0)
              | k1_xboole_0 = X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | v1_tops_1(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( r1_xboole_0(X1,X2)
                  & v3_pre_topc(X2,X0)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( ~ r1_xboole_0(X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v1_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,sK3)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
            | ~ v1_tops_1(X1,sK3) )
          & ( ! [X3] :
                ( ~ r1_xboole_0(X1,X3)
                | ~ v3_pre_topc(X3,sK3)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
            | v1_tops_1(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ( ( r1_xboole_0(sK4,sK5)
        & v3_pre_topc(sK5,sK3)
        & k1_xboole_0 != sK5
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) )
      | ~ v1_tops_1(sK4,sK3) )
    & ( ! [X3] :
          ( ~ r1_xboole_0(sK4,X3)
          | ~ v3_pre_topc(X3,sK3)
          | k1_xboole_0 = X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
      | v1_tops_1(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f62,f65,f64,f63])).

fof(f99,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(sK4,X3)
      | ~ v3_pre_topc(X3,sK3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
      | v1_tops_1(sK4,sK3) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ~ ( r1_xboole_0(X1,X3)
                        & r2_hidden(X2,X3)
                        & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_xboole_0(X1,X3)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK2(X0,X1,X2))
        & r2_hidden(X2,sK2(X0,X1,X2))
        & v3_pre_topc(sK2(X0,X1,X2),X0)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( r1_xboole_0(X1,sK2(X0,X1,X2))
                    & r2_hidden(X2,sK2(X0,X1,X2))
                    & v3_pre_topc(sK2(X0,X1,X2),X0)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f56,f57])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_xboole_0(X1,sK2(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f96,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f97,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f78,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f82,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f98,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f66])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f53])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f70,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f94,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f100,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tops_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f101,plain,
    ( k1_xboole_0 != sK5
    | ~ v1_tops_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f103,plain,
    ( r1_xboole_0(sK4,sK5)
    | ~ v1_tops_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X4)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f102,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ v1_tops_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => m1_subset_1(o_2_1_tops_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | v3_pre_topc(sK2(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r2_hidden(X2,sK2(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3338,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_33,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ r1_xboole_0(sK4,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tops_1(sK4,sK3)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_18,plain,
    ( r1_xboole_0(X0,sK2(X1,X0,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_792,plain,
    ( r1_xboole_0(X0,sK2(X1,X0,X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_36])).

cnf(c_793,plain,
    ( r1_xboole_0(X0,sK2(sK3,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_792])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_797,plain,
    ( v2_struct_0(sK3)
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_xboole_0(X0,sK2(sK3,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_793,c_35])).

cnf(c_798,plain,
    ( r1_xboole_0(X0,sK2(sK3,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | v2_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_797])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_15,plain,
    ( ~ v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_486,plain,
    ( ~ v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_11,c_15])).

cnf(c_884,plain,
    ( ~ v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_486,c_35])).

cnf(c_885,plain,
    ( ~ v2_struct_0(sK3)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_884])).

cnf(c_1089,plain,
    ( r1_xboole_0(X0,sK2(sK3,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_798,c_885])).

cnf(c_1253,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | v1_tops_1(sK4,sK3)
    | r2_hidden(X2,k2_pre_topc(sK3,X1))
    | v1_xboole_0(u1_struct_0(sK3))
    | sK2(sK3,X1,X2) != X0
    | sK4 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_1089])).

cnf(c_1254,plain,
    ( ~ v3_pre_topc(sK2(sK3,sK4,X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tops_1(sK4,sK3)
    | r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | v1_xboole_0(u1_struct_0(sK3))
    | k1_xboole_0 = sK2(sK3,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_1253])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1258,plain,
    ( ~ m1_subset_1(sK2(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v3_pre_topc(sK2(sK3,sK4,X0),sK3)
    | v1_tops_1(sK4,sK3)
    | r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | v1_xboole_0(u1_struct_0(sK3))
    | k1_xboole_0 = sK2(sK3,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1254,c_34])).

cnf(c_1259,plain,
    ( ~ v3_pre_topc(sK2(sK3,sK4,X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tops_1(sK4,sK3)
    | r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | v1_xboole_0(u1_struct_0(sK3))
    | k1_xboole_0 = sK2(sK3,sK4,X0) ),
    inference(renaming,[status(thm)],[c_1258])).

cnf(c_3325,plain,
    ( ~ v3_pre_topc(sK2(sK3,sK4,X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | k1_xboole_0 = sK2(sK3,sK4,X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1259])).

cnf(c_10,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_500,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_11,c_10])).

cnf(c_877,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_500,c_35])).

cnf(c_878,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_877])).

cnf(c_4117,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_878])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_4127,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8398,plain,
    ( r1_tarski(k2_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4117,c_4127])).

cnf(c_14,plain,
    ( m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_4130,plain,
    ( m1_subset_1(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_4129,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4835,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4130,c_4129])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4132,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5578,plain,
    ( r2_hidden(sK1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4835,c_4132])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_4124,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6857,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5578,c_4124])).

cnf(c_8600,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8398,c_6857])).

cnf(c_8607,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(k2_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8600])).

cnf(c_3331,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3330,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7297,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_3331,c_3330])).

cnf(c_3,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_511,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_11,c_3])).

cnf(c_872,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_511,c_35])).

cnf(c_873,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_872])).

cnf(c_11545,plain,
    ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_7297,c_873])).

cnf(c_3339,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_12013,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(k2_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_11545,c_3339])).

cnf(c_8427,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_3338,c_3330])).

cnf(c_27,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_13869,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k1_xboole_0,X1)
    | ~ v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_8427,c_27])).

cnf(c_25,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tops_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_7144,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v1_tops_1(sK4,sK3)
    | ~ r2_hidden(X0,sK5) ),
    inference(resolution,[status(thm)],[c_25,c_32])).

cnf(c_34740,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK3))
    | ~ v1_tops_1(sK4,sK3)
    | ~ r2_hidden(X0,sK5)
    | ~ v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_13869,c_7144])).

cnf(c_4121,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_tops_1(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4126,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5134,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | v1_tops_1(sK4,sK3) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4121,c_4126])).

cnf(c_11266,plain,
    ( v1_tops_1(sK4,sK3) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5134,c_4129])).

cnf(c_31,negated_conjecture,
    ( ~ v1_tops_1(sK4,sK3)
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_4502,plain,
    ( ~ v1_tops_1(sK4,sK3)
    | ~ v1_xboole_0(sK5) ),
    inference(resolution,[status(thm)],[c_31,c_27])).

cnf(c_4503,plain,
    ( v1_tops_1(sK4,sK3) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4502])).

cnf(c_3334,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_918,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(X0,X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_35])).

cnf(c_919,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tops_1(X0,sK3)
    | k2_pre_topc(sK3,X0) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_918])).

cnf(c_7348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tops_1(X0,sK3)
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | ~ r2_hidden(X2,k2_struct_0(sK3))
    | X1 != X2 ),
    inference(resolution,[status(thm)],[c_3334,c_919])).

cnf(c_9312,plain,
    ( ~ v1_tops_1(sK4,sK3)
    | r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | ~ r2_hidden(X1,k2_struct_0(sK3))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_7348,c_34])).

cnf(c_9490,plain,
    ( ~ v1_tops_1(sK4,sK3)
    | r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | ~ r2_hidden(X0,k2_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_9312,c_3330])).

cnf(c_29,negated_conjecture,
    ( r1_xboole_0(sK4,sK5)
    | ~ v1_tops_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_22,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ r1_xboole_0(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,X0)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_700,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ r1_xboole_0(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,X0)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_36])).

cnf(c_701,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ r1_xboole_0(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(sK3,X1))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_700])).

cnf(c_705,plain,
    ( v2_struct_0(sK3)
    | ~ r2_hidden(X2,k2_pre_topc(sK3,X1))
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_xboole_0(X1,X0)
    | ~ v3_pre_topc(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_701,c_35])).

cnf(c_706,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ r1_xboole_0(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(sK3,X1))
    | v2_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_705])).

cnf(c_727,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ r1_xboole_0(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(sK3,X1))
    | v2_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_706,c_25])).

cnf(c_1149,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ r1_xboole_0(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(sK3,X1))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_727,c_885])).

cnf(c_1229,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tops_1(sK4,sK3)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(sK3,X1))
    | v1_xboole_0(u1_struct_0(sK3))
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1149])).

cnf(c_1230,plain,
    ( ~ v3_pre_topc(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tops_1(sK4,sK3)
    | ~ r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | ~ r2_hidden(X0,sK5)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1229])).

cnf(c_30,negated_conjecture,
    ( v3_pre_topc(sK5,sK3)
    | ~ v1_tops_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1234,plain,
    ( ~ v1_tops_1(sK4,sK3)
    | ~ r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | ~ r2_hidden(X0,sK5)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1230,c_34,c_32,c_30])).

cnf(c_3327,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | ~ r2_hidden(X0,sK5)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1234])).

cnf(c_10123,plain,
    ( ~ v1_tops_1(sK4,sK3)
    | ~ r2_hidden(X0,k2_struct_0(sK3))
    | ~ r2_hidden(X0,sK5)
    | ~ sP1_iProver_split ),
    inference(resolution,[status(thm)],[c_9490,c_3327])).

cnf(c_5264,plain,
    ( r1_tarski(k2_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_24,c_878])).

cnf(c_6071,plain,
    ( r2_hidden(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X0,k2_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_6,c_5264])).

cnf(c_7008,plain,
    ( ~ r2_hidden(X0,k2_struct_0(sK3))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_6071,c_28])).

cnf(c_10448,plain,
    ( ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(X0,k2_struct_0(sK3))
    | ~ v1_tops_1(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10123,c_1234,c_7008,c_9490])).

cnf(c_10449,plain,
    ( ~ v1_tops_1(sK4,sK3)
    | ~ r2_hidden(X0,k2_struct_0(sK3))
    | ~ r2_hidden(X0,sK5) ),
    inference(renaming,[status(thm)],[c_10448])).

cnf(c_10450,plain,
    ( v1_tops_1(sK4,sK3) != iProver_top
    | r2_hidden(X0,k2_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10449])).

cnf(c_4691,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | v1_tops_1(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_873,c_4121])).

cnf(c_6014,plain,
    ( m1_subset_1(X0,k2_struct_0(sK3)) = iProver_top
    | v1_tops_1(sK4,sK3) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4691,c_4126])).

cnf(c_11531,plain,
    ( v1_tops_1(sK4,sK3) != iProver_top
    | r2_hidden(X0,k2_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6014,c_4129])).

cnf(c_4692,plain,
    ( v1_tops_1(sK4,sK3) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4121,c_4127])).

cnf(c_5719,plain,
    ( v1_tops_1(sK4,sK3) != iProver_top
    | r1_tarski(sK5,k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_873,c_4692])).

cnf(c_15187,plain,
    ( v1_tops_1(sK4,sK3) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5719,c_6857])).

cnf(c_16951,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_tops_1(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11266,c_4503,c_10450,c_11531,c_15187])).

cnf(c_16952,plain,
    ( v1_tops_1(sK4,sK3) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_16951])).

cnf(c_16953,plain,
    ( ~ v1_tops_1(sK4,sK3)
    | ~ r2_hidden(X0,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16952])).

cnf(c_39353,plain,
    ( ~ r2_hidden(X0,sK5)
    | ~ v1_tops_1(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34740,c_16953])).

cnf(c_39354,plain,
    ( ~ v1_tops_1(sK4,sK3)
    | ~ r2_hidden(X0,sK5) ),
    inference(renaming,[status(thm)],[c_39353])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(o_2_1_tops_1(X1,X0),X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_819,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(o_2_1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_36])).

cnf(c_820,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(o_2_1_tops_1(sK3,X0),X0)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_819])).

cnf(c_824,plain,
    ( m1_subset_1(o_2_1_tops_1(sK3,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_820,c_35])).

cnf(c_825,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(o_2_1_tops_1(sK3,X0),X0) ),
    inference(renaming,[status(thm)],[c_824])).

cnf(c_5409,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(o_2_1_tops_1(sK3,X0),X0)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_17,c_825])).

cnf(c_5747,plain,
    ( ~ v1_tops_1(sK4,sK3)
    | r2_hidden(o_2_1_tops_1(sK3,sK5),sK5)
    | v1_xboole_0(sK5) ),
    inference(resolution,[status(thm)],[c_5409,c_32])).

cnf(c_5868,plain,
    ( r2_hidden(o_2_1_tops_1(sK3,sK5),sK5)
    | ~ v1_tops_1(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5747,c_4502])).

cnf(c_5869,plain,
    ( ~ v1_tops_1(sK4,sK3)
    | r2_hidden(o_2_1_tops_1(sK3,sK5),sK5) ),
    inference(renaming,[status(thm)],[c_5868])).

cnf(c_39369,plain,
    ( ~ v1_tops_1(sK4,sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_39354,c_5869])).

cnf(c_3326,plain,
    ( v1_tops_1(sK4,sK3)
    | v1_xboole_0(u1_struct_0(sK3))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1259])).

cnf(c_39374,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | sP0_iProver_split ),
    inference(backward_subsumption_resolution,[status(thm)],[c_39369,c_3326])).

cnf(c_50115,plain,
    ( v1_xboole_0(k2_struct_0(sK3))
    | sP0_iProver_split ),
    inference(resolution,[status(thm)],[c_12013,c_39374])).

cnf(c_7293,plain,
    ( ~ v1_xboole_0(X0)
    | X1 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution,[status(thm)],[c_3331,c_27])).

cnf(c_12803,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tops_1(X0,sK3)
    | ~ v1_xboole_0(k2_struct_0(sK3))
    | k1_xboole_0 = k2_pre_topc(sK3,X0) ),
    inference(resolution,[status(thm)],[c_7293,c_919])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_5249,plain,
    ( r1_tarski(X0,X1)
    | ~ v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_5,c_28])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_933,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_1(X0,X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_35])).

cnf(c_934,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tops_1(X0,sK3)
    | k2_pre_topc(sK3,X0) != k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_933])).

cnf(c_7128,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tops_1(X0,sK3)
    | ~ r1_tarski(k2_pre_topc(sK3,X0),k2_struct_0(sK3))
    | ~ r1_tarski(k2_struct_0(sK3),k2_pre_topc(sK3,X0)) ),
    inference(resolution,[status(thm)],[c_0,c_934])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_906,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_35])).

cnf(c_907,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_pre_topc(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_906])).

cnf(c_4115,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_907])).

cnf(c_7533,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,X0),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4115,c_4127])).

cnf(c_7656,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,X0),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_873,c_7533])).

cnf(c_7661,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(k2_pre_topc(sK3,X0),k2_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7656])).

cnf(c_8980,plain,
    ( v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(k2_struct_0(sK3),k2_pre_topc(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7128,c_7661])).

cnf(c_8981,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tops_1(X0,sK3)
    | ~ r1_tarski(k2_struct_0(sK3),k2_pre_topc(sK3,X0)) ),
    inference(renaming,[status(thm)],[c_8980])).

cnf(c_9766,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tops_1(X0,sK3)
    | ~ v1_xboole_0(k2_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_5249,c_8981])).

cnf(c_13738,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(k2_struct_0(sK3))
    | k1_xboole_0 = k2_pre_topc(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12803,c_9766])).

cnf(c_4516,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_6039,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_xboole_0(k2_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_3339,c_873])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_6079,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(X0))
    | ~ r1_tarski(k2_struct_0(sK3),X0) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_7038,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | X0 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3339])).

cnf(c_4133,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_288,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_289,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_288])).

cnf(c_363,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_26,c_289])).

cnf(c_4119,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_6965,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4133,c_4119])).

cnf(c_8599,plain,
    ( r1_tarski(k2_struct_0(sK3),X0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8398,c_6965])).

cnf(c_8604,plain,
    ( r1_tarski(k2_struct_0(sK3),X0)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8599])).

cnf(c_11995,plain,
    ( X0 != u1_struct_0(sK3)
    | k2_struct_0(sK3) = X0 ),
    inference(resolution,[status(thm)],[c_11545,c_3331])).

cnf(c_12390,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),X0)
    | X0 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_13873,plain,
    ( m1_subset_1(u1_struct_0(sK3),X0)
    | ~ m1_subset_1(k2_struct_0(sK3),X0) ),
    inference(resolution,[status(thm)],[c_8427,c_873])).

cnf(c_14079,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(X0))
    | r1_tarski(u1_struct_0(sK3),X0) ),
    inference(resolution,[status(thm)],[c_13873,c_24])).

cnf(c_4120,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_7534,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X1,k2_pre_topc(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4115,c_4126])).

cnf(c_13789,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,k2_pre_topc(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4120,c_7534])).

cnf(c_13827,plain,
    ( m1_subset_1(sK0(k2_pre_topc(sK3,sK4),X0),u1_struct_0(sK3)) = iProver_top
    | r1_tarski(k2_pre_topc(sK3,sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4133,c_13789])).

cnf(c_14311,plain,
    ( r2_hidden(sK0(k2_pre_topc(sK3,sK4),X0),u1_struct_0(sK3)) = iProver_top
    | r1_tarski(k2_pre_topc(sK3,sK4),X0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13827,c_4129])).

cnf(c_15570,plain,
    ( r2_hidden(sK0(k2_pre_topc(sK3,sK4),X0),X1) = iProver_top
    | r1_tarski(k2_pre_topc(sK3,sK4),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK3),X1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14311,c_4132])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4134,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_15568,plain,
    ( r1_tarski(k2_pre_topc(sK3,sK4),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14311,c_4134])).

cnf(c_39,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4222,plain,
    ( m1_subset_1(k2_pre_topc(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_907])).

cnf(c_4223,plain,
    ( m1_subset_1(k2_pre_topc(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4222])).

cnf(c_7065,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(k2_pre_topc(sK3,sK4),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4516])).

cnf(c_7066,plain,
    ( m1_subset_1(k2_pre_topc(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7065])).

cnf(c_15881,plain,
    ( r1_tarski(k2_pre_topc(sK3,sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15568,c_39,c_4223,c_7066])).

cnf(c_15886,plain,
    ( r1_tarski(k2_pre_topc(sK3,sK4),X0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15881,c_6965])).

cnf(c_22044,plain,
    ( r1_tarski(u1_struct_0(sK3),X1) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,sK4),X0) = iProver_top
    | r2_hidden(sK0(k2_pre_topc(sK3,sK4),X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15570,c_15886])).

cnf(c_22045,plain,
    ( r2_hidden(sK0(k2_pre_topc(sK3,sK4),X0),X1) = iProver_top
    | r1_tarski(k2_pre_topc(sK3,sK4),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK3),X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_22044])).

cnf(c_22050,plain,
    ( r1_tarski(k2_pre_topc(sK3,sK4),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22045,c_4134])).

cnf(c_4621,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4133,c_4124])).

cnf(c_4136,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5506,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4621,c_4136])).

cnf(c_22237,plain,
    ( k2_pre_topc(sK3,sK4) = X0
    | r1_tarski(u1_struct_0(sK3),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22050,c_5506])).

cnf(c_22259,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),X0)
    | ~ v1_xboole_0(X0)
    | k2_pre_topc(sK3,sK4) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22237])).

cnf(c_4359,plain,
    ( k2_pre_topc(sK3,X0) != X1
    | k2_pre_topc(sK3,X0) = k2_struct_0(sK3)
    | k2_struct_0(sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_3331])).

cnf(c_48877,plain,
    ( k2_pre_topc(sK3,sK4) != X0
    | k2_pre_topc(sK3,sK4) = k2_struct_0(sK3)
    | k2_struct_0(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_4359])).

cnf(c_48880,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tops_1(sK4,sK3)
    | k2_pre_topc(sK3,sK4) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_50372,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13738,c_34,c_4516,c_6039,c_6079,c_7038,c_8604,c_11995,c_12390,c_14079,c_22259,c_39369,c_48877,c_48880])).

cnf(c_50373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(k2_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_50372])).

cnf(c_50394,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_50373,c_14])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_738,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_36])).

cnf(c_739,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_738])).

cnf(c_743,plain,
    ( v2_struct_0(sK3)
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | m1_subset_1(sK2(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_739,c_35])).

cnf(c_744,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | v2_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_743])).

cnf(c_1129,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_744,c_885])).

cnf(c_72305,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_20,plain,
    ( v3_pre_topc(sK2(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k2_pre_topc(X0,X1))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_673,plain,
    ( v3_pre_topc(sK2(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k2_pre_topc(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_36])).

cnf(c_674,plain,
    ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_673])).

cnf(c_678,plain,
    ( v2_struct_0(sK3)
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(sK2(sK3,X0,X1),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_674,c_35])).

cnf(c_679,plain,
    ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | v2_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_678])).

cnf(c_1175,plain,
    ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_679,c_885])).

cnf(c_72464,plain,
    ( v3_pre_topc(sK2(sK3,sK4,X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1175])).

cnf(c_110354,plain,
    ( k1_xboole_0 = sK2(sK3,sK4,X0)
    | r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3325,c_34,c_8607,c_31661,c_39369,c_48880,c_50394,c_72305,c_72464])).

cnf(c_110355,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | k1_xboole_0 = sK2(sK3,sK4,X0) ),
    inference(renaming,[status(thm)],[c_110354])).

cnf(c_120442,plain,
    ( ~ m1_subset_1(X0,sK2(sK3,sK4,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(X2,k1_xboole_0)
    | r2_hidden(X1,k2_pre_topc(sK3,sK4))
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_3338,c_110355])).

cnf(c_123178,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(X1,k1_xboole_0)
    | ~ m1_subset_1(sK2(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | X1 != o_2_1_tops_1(sK3,sK2(sK3,sK4,X0)) ),
    inference(resolution,[status(thm)],[c_120442,c_825])).

cnf(c_12,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_553,plain,
    ( k1_xboole_0 = X0
    | o_0_0_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_554,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_4396,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | X0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3339])).

cnf(c_8566,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k1_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4396])).

cnf(c_4111,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r2_hidden(X1,k2_pre_topc(sK3,X0)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1129])).

cnf(c_4118,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(o_2_1_tops_1(sK3,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_825])).

cnf(c_8933,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(o_2_1_tops_1(sK3,sK2(sK3,X0,X1)),sK2(sK3,X0,X1)) = iProver_top
    | r2_hidden(X1,k2_pre_topc(sK3,X0)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4111,c_4118])).

cnf(c_11701,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | k1_xboole_0 = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_11702,plain,
    ( k1_xboole_0 = u1_struct_0(sK3)
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11701])).

cnf(c_4747,plain,
    ( X0 != X1
    | k2_struct_0(sK3) != X1
    | k2_struct_0(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_3331])).

cnf(c_7768,plain,
    ( k2_struct_0(sK3) != X0
    | k2_struct_0(sK3) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_4747])).

cnf(c_22196,plain,
    ( k2_struct_0(sK3) != u1_struct_0(sK3)
    | k2_struct_0(sK3) = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_7768])).

cnf(c_12656,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3339])).

cnf(c_36117,plain,
    ( v1_xboole_0(k2_struct_0(sK3))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_struct_0(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12656])).

cnf(c_72874,plain,
    ( r2_hidden(X1,k2_pre_topc(sK3,X0)) = iProver_top
    | m1_subset_1(o_2_1_tops_1(sK3,sK2(sK3,X0,X1)),sK2(sK3,X0,X1)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8933,c_12,c_554,c_8566,c_11545,c_11702,c_22196,c_36117,c_50394])).

cnf(c_72875,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(o_2_1_tops_1(sK3,sK2(sK3,X0,X1)),sK2(sK3,X0,X1)) = iProver_top
    | r2_hidden(X1,k2_pre_topc(sK3,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_72874])).

cnf(c_72880,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK3,X0)) = iProver_top
    | r2_hidden(o_2_1_tops_1(sK3,sK2(sK3,X0,X1)),sK2(sK3,X0,X1)) = iProver_top
    | v1_xboole_0(sK2(sK3,X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_72875,c_4129])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK2(X1,X0,X2))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_765,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK2(X1,X0,X2))
    | r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_36])).

cnf(c_766,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,sK2(sK3,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_765])).

cnf(c_770,plain,
    ( v2_struct_0(sK3)
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | r2_hidden(X1,sK2(sK3,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_766,c_35])).

cnf(c_771,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,sK2(sK3,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | v2_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_770])).

cnf(c_1109,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,sK2(sK3,X0,X1))
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_771,c_885])).

cnf(c_5178,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | ~ v1_xboole_0(sK2(sK3,X0,X1))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_28,c_1109])).

cnf(c_5179,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK3,X0)) = iProver_top
    | v1_xboole_0(sK2(sK3,X0,X1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5178])).

cnf(c_5753,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,k2_pre_topc(sK3,X0))
    | r2_hidden(o_2_1_tops_1(sK3,sK2(sK3,X0,X1)),sK2(sK3,X0,X1))
    | v1_xboole_0(sK2(sK3,X0,X1))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_5409,c_1129])).

cnf(c_5754,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK3,X0)) = iProver_top
    | r2_hidden(o_2_1_tops_1(sK3,sK2(sK3,X0,X1)),sK2(sK3,X0,X1)) = iProver_top
    | v1_xboole_0(sK2(sK3,X0,X1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5753])).

cnf(c_73175,plain,
    ( r2_hidden(o_2_1_tops_1(sK3,sK2(sK3,X0,X1)),sK2(sK3,X0,X1)) = iProver_top
    | r2_hidden(X1,k2_pre_topc(sK3,X0)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_72880,c_12,c_554,c_5179,c_5754,c_8566,c_11545,c_11702,c_22196,c_36117,c_50394])).

cnf(c_73176,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK3,X0)) = iProver_top
    | r2_hidden(o_2_1_tops_1(sK3,sK2(sK3,X0,X1)),sK2(sK3,X0,X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_73175])).

cnf(c_73183,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK3,X0)) = iProver_top
    | v1_xboole_0(sK2(sK3,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_73176,c_4124])).

cnf(c_73213,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK3,sK4)) = iProver_top
    | v1_xboole_0(sK2(sK3,sK4,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4120,c_73183])).

cnf(c_73244,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | ~ v1_xboole_0(sK2(sK3,sK4,X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_73213])).

cnf(c_117786,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_3331,c_3330])).

cnf(c_124405,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | sK2(sK3,sK4,X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_117786,c_110355])).

cnf(c_124872,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | v1_xboole_0(sK2(sK3,sK4,X0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_124405,c_3339])).

cnf(c_124895,plain,
    ( r2_hidden(X0,k2_pre_topc(sK3,sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_123178,c_12,c_554,c_8566,c_73244,c_124872])).

cnf(c_124896,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,k2_pre_topc(sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_124895])).

cnf(c_125513,plain,
    ( ~ m1_subset_1(sK0(X0,k2_pre_topc(sK3,sK4)),u1_struct_0(sK3))
    | r1_tarski(X0,k2_pre_topc(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_124896,c_4])).

cnf(c_117340,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X0,k2_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_25,c_878])).

cnf(c_158892,plain,
    ( ~ r2_hidden(sK0(X0,k2_pre_topc(sK3,sK4)),k2_struct_0(sK3))
    | r1_tarski(X0,k2_pre_topc(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_125513,c_117340])).

cnf(c_164521,plain,
    ( r1_tarski(k2_struct_0(sK3),k2_pre_topc(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_158892,c_5])).

cnf(c_4352,plain,
    ( ~ r1_tarski(k2_pre_topc(sK3,X0),k2_struct_0(sK3))
    | ~ r1_tarski(k2_struct_0(sK3),k2_pre_topc(sK3,X0))
    | k2_pre_topc(sK3,X0) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_51757,plain,
    ( ~ r1_tarski(k2_pre_topc(sK3,sK4),k2_struct_0(sK3))
    | ~ r1_tarski(k2_struct_0(sK3),k2_pre_topc(sK3,sK4))
    | k2_pre_topc(sK3,sK4) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4352])).

cnf(c_15885,plain,
    ( r1_tarski(k2_pre_topc(sK3,sK4),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_873,c_15881])).

cnf(c_15892,plain,
    ( r1_tarski(k2_pre_topc(sK3,sK4),k2_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15885])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_164521,c_51757,c_48880,c_39369,c_15892,c_34])).


%------------------------------------------------------------------------------
