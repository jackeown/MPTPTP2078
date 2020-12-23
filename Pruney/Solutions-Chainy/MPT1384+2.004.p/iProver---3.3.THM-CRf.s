%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:24 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 7.79s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_5571)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_tarski(X3,X1)
                              & m1_connsp_2(X3,X0,X2) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ? [X5] :
                    ( r1_tarski(X5,X1)
                    & m1_connsp_2(X5,X0,X4)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f49])).

fof(f54,plain,(
    ! [X0,X1,X4] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK5(X4),X1)
        & m1_connsp_2(sK5(X4),X0,X4)
        & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X1)
              | ~ m1_connsp_2(X3,X0,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_tarski(X3,X1)
            | ~ m1_connsp_2(X3,X0,sK4)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK4,X1)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ? [X5] :
                    ( r1_tarski(X5,X1)
                    & m1_connsp_2(X5,X0,X4)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,sK3)
                  | ~ m1_connsp_2(X3,X0,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,sK3)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v3_pre_topc(sK3,X0) )
        & ( ! [X4] :
              ( ? [X5] :
                  ( r1_tarski(X5,sK3)
                  & m1_connsp_2(X5,X0,X4)
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X4,sK3)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | v3_pre_topc(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( r1_tarski(X5,X1)
                      & m1_connsp_2(X5,X0,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,sK2,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(sK2)) )
            | ~ v3_pre_topc(X1,sK2) )
          & ( ! [X4] :
                ( ? [X5] :
                    ( r1_tarski(X5,X1)
                    & m1_connsp_2(X5,sK2,X4)
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2))) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
            | v3_pre_topc(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ( ( ! [X3] :
            ( ~ r1_tarski(X3,sK3)
            | ~ m1_connsp_2(X3,sK2,sK4)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        & r2_hidden(sK4,sK3)
        & m1_subset_1(sK4,u1_struct_0(sK2)) )
      | ~ v3_pre_topc(sK3,sK2) )
    & ( ! [X4] :
          ( ( r1_tarski(sK5(X4),sK3)
            & m1_connsp_2(sK5(X4),sK2,X4)
            & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2))) )
          | ~ r2_hidden(X4,sK3)
          | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
      | v3_pre_topc(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f50,f54,f53,f52,f51])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK3)
      | ~ m1_connsp_2(X3,sK2,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f87,plain,
    ( r2_hidden(sK4,sK3)
    | ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    ! [X4] :
      ( m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X4] :
      ( r1_tarski(sK5(X4),sK3)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    ! [X4] :
      ( m1_connsp_2(sK5(X4),sK2,X4)
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | v3_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_16,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2365,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_8,c_16])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_14362,plain,
    ( m1_connsp_2(sK3,sK2,X0)
    | ~ v3_pre_topc(sK3,sK2)
    | ~ r2_hidden(X0,sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_2365,c_29])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_34,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_12,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_586,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != X0
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_12])).

cnf(c_587,plain,
    ( sP3_iProver_split
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_12])).

cnf(c_585,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_12])).

cnf(c_914,plain,
    ( k1_tops_1(X1,X0) != X0
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_586,c_587,c_585])).

cnf(c_915,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != X0 ),
    inference(renaming,[status(thm)],[c_914])).

cnf(c_1891,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k1_tops_1(sK2,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_915])).

cnf(c_1892,plain,
    ( k1_tops_1(sK2,sK3) != sK3
    | v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1891])).

cnf(c_1381,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_583,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_13])).

cnf(c_1398,plain,
    ( k1_tops_1(X0,X1) = X1
    | v3_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_584,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_13])).

cnf(c_632,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_584])).

cnf(c_633,plain,
    ( k1_tops_1(X0,X1) = X1
    | v3_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_13])).

cnf(c_2382,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_2383,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2382])).

cnf(c_5940,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v3_pre_topc(X1,X0) != iProver_top
    | k1_tops_1(X0,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1398,c_34,c_35,c_36,c_632,c_633,c_2383])).

cnf(c_5941,plain,
    ( k1_tops_1(X0,X1) = X1
    | v3_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5940])).

cnf(c_5954,plain,
    ( k1_tops_1(sK2,sK3) = sK3
    | v3_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1381,c_5941])).

cnf(c_6306,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top
    | k1_tops_1(sK2,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5954,c_34,c_35,c_36,c_632,c_2383,c_5571])).

cnf(c_6307,plain,
    ( k1_tops_1(sK2,sK3) = sK3
    | v3_pre_topc(sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6306])).

cnf(c_6308,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | k1_tops_1(sK2,sK3) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6307])).

cnf(c_1394,plain,
    ( m1_connsp_2(X0,X1,X2) = iProver_top
    | v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1406,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1672,plain,
    ( m1_connsp_2(X0,X1,X2) = iProver_top
    | v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1394,c_1406])).

cnf(c_10456,plain,
    ( m1_connsp_2(sK3,sK2,X0) = iProver_top
    | v3_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1381,c_1672])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_33,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_10908,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | v3_pre_topc(sK3,sK2) != iProver_top
    | m1_connsp_2(sK3,sK2,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10456,c_33,c_34,c_35])).

cnf(c_10909,plain,
    ( m1_connsp_2(sK3,sK2,X0) = iProver_top
    | v3_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_10908])).

cnf(c_23,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK2,sK4)
    | ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1387,plain,
    ( m1_connsp_2(X0,sK2,sK4) != iProver_top
    | v3_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1905,plain,
    ( m1_connsp_2(sK3,sK2,sK4) != iProver_top
    | v3_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1381,c_1387])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2218,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2219,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2218])).

cnf(c_2333,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top
    | m1_connsp_2(sK3,sK2,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1905,c_2219])).

cnf(c_2334,plain,
    ( m1_connsp_2(sK3,sK2,sK4) != iProver_top
    | v3_pre_topc(sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2333])).

cnf(c_10918,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10909,c_2334])).

cnf(c_24,negated_conjecture,
    ( ~ v3_pre_topc(sK3,sK2)
    | r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_47,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_11102,plain,
    ( v3_pre_topc(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10918,c_47])).

cnf(c_14862,plain,
    ( ~ v3_pre_topc(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14362,c_34,c_35,c_36,c_47,c_1892,c_6308,c_10918])).

cnf(c_15,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2375,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3) ),
    inference(resolution,[status(thm)],[c_8,c_29])).

cnf(c_28,negated_conjecture,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2483,plain,
    ( v3_pre_topc(sK3,sK2)
    | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2375,c_28])).

cnf(c_5370,plain,
    ( ~ m1_connsp_2(sK5(X0),sK2,X1)
    | v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
    | ~ r2_hidden(X0,sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_15,c_2483])).

cnf(c_1382,plain,
    ( v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1395,plain,
    ( m1_connsp_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,k1_tops_1(X1,X0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4910,plain,
    ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
    | v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,sK5(X0))) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1382,c_1395])).

cnf(c_5371,plain,
    ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
    | v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,sK5(X0))) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5370])).

cnf(c_5433,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,sK5(X0))) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
    | v3_pre_topc(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4910,c_33,c_34,c_35,c_5371])).

cnf(c_5434,plain,
    ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
    | v3_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK2,sK5(X0))) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_5433])).

cnf(c_5435,plain,
    ( ~ m1_connsp_2(sK5(X0),sK2,X1)
    | v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
    | ~ r2_hidden(X0,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5434])).

cnf(c_5734,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v3_pre_topc(sK3,sK2)
    | ~ m1_connsp_2(sK5(X0),sK2,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5370,c_5435])).

cnf(c_5735,plain,
    ( ~ m1_connsp_2(sK5(X0),sK2,X1)
    | v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
    | ~ r2_hidden(X0,sK3) ),
    inference(renaming,[status(thm)],[c_5734])).

cnf(c_14905,plain,
    ( ~ m1_connsp_2(sK5(X0),sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
    | ~ r2_hidden(X0,sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_14862,c_5735])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_4000,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,k1_tops_1(X1,X0))
    | r2_hidden(X3,k1_tops_1(X1,X2))
    | ~ r1_tarski(X0,X2)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_11,c_2])).

cnf(c_16942,plain,
    ( ~ m1_connsp_2(sK5(X0),sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ r2_hidden(X0,sK3)
    | ~ r1_tarski(sK5(X0),X2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_14905,c_4000])).

cnf(c_14900,plain,
    ( m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_14862,c_2483])).

cnf(c_25938,plain,
    ( ~ r1_tarski(sK5(X0),X2)
    | ~ r2_hidden(X0,sK3)
    | r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ m1_connsp_2(sK5(X0),sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16942,c_34,c_30,c_35,c_36,c_47,c_1892,c_2483,c_6308,c_6634,c_10918])).

cnf(c_25939,plain,
    ( ~ m1_connsp_2(sK5(X0),sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k1_tops_1(sK2,X2))
    | ~ r2_hidden(X0,sK3)
    | ~ r1_tarski(sK5(X0),X2) ),
    inference(renaming,[status(thm)],[c_25938])).

cnf(c_25990,plain,
    ( ~ m1_connsp_2(sK5(X0),sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,sK3))
    | ~ r2_hidden(X0,sK3)
    | ~ r1_tarski(sK5(X0),sK3) ),
    inference(resolution,[status(thm)],[c_25939,c_29])).

cnf(c_26,negated_conjecture,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3)
    | r1_tarski(sK5(X0),sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2481,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ r2_hidden(X0,sK3)
    | r1_tarski(sK5(X0),sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2375,c_26])).

cnf(c_25999,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(X1,k1_tops_1(sK2,sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_connsp_2(sK5(X0),sK2,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25990,c_34,c_35,c_36,c_47,c_1892,c_2481,c_6308,c_10918])).

cnf(c_26000,plain,
    ( ~ m1_connsp_2(sK5(X0),sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,sK3))
    | ~ r2_hidden(X0,sK3) ),
    inference(renaming,[status(thm)],[c_25999])).

cnf(c_27,negated_conjecture,
    ( m1_connsp_2(sK5(X0),sK2,X0)
    | v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2482,plain,
    ( m1_connsp_2(sK5(X0),sK2,X0)
    | v3_pre_topc(sK3,sK2)
    | ~ r2_hidden(X0,sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2375,c_27])).

cnf(c_14881,plain,
    ( m1_connsp_2(sK5(X0),sK2,X0)
    | ~ r2_hidden(X0,sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_14862,c_2482])).

cnf(c_26195,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(X0,k1_tops_1(sK2,sK3))
    | ~ r2_hidden(X0,sK3) ),
    inference(resolution,[status(thm)],[c_26000,c_14881])).

cnf(c_26208,plain,
    ( r2_hidden(X0,k1_tops_1(sK2,sK3))
    | ~ r2_hidden(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26195,c_2375])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27078,plain,
    ( ~ r2_hidden(sK0(X0,k1_tops_1(sK2,sK3)),sK3)
    | r1_tarski(X0,k1_tops_1(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_26208,c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_28327,plain,
    ( r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_27078,c_1])).

cnf(c_1412,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1405,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3417,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,k1_tops_1(X1,X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1405,c_1406])).

cnf(c_12117,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK3)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1381,c_3417])).

cnf(c_12289,plain,
    ( r2_hidden(X0,k1_tops_1(sK2,sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12117,c_35])).

cnf(c_12290,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12289])).

cnf(c_12297,plain,
    ( m1_subset_1(sK0(k1_tops_1(sK2,sK3),X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k1_tops_1(sK2,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_12290])).

cnf(c_17,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1393,plain,
    ( m1_connsp_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3645,plain,
    ( m1_connsp_2(sK3,sK2,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1381,c_1393])).

cnf(c_4130,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_connsp_2(sK3,sK2,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3645,c_33,c_34,c_35])).

cnf(c_4131,plain,
    ( m1_connsp_2(sK3,sK2,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4130])).

cnf(c_13608,plain,
    ( m1_connsp_2(sK3,sK2,sK0(k1_tops_1(sK2,sK3),X0)) != iProver_top
    | r2_hidden(sK0(k1_tops_1(sK2,sK3),X0),sK3) = iProver_top
    | r1_tarski(k1_tops_1(sK2,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12297,c_4131])).

cnf(c_14,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1396,plain,
    ( m1_connsp_2(X0,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,k1_tops_1(X1,X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5113,plain,
    ( m1_connsp_2(sK3,sK2,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1381,c_1396])).

cnf(c_5412,plain,
    ( r2_hidden(X0,k1_tops_1(sK2,sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_connsp_2(sK3,sK2,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5113,c_33,c_34,c_35])).

cnf(c_5413,plain,
    ( m1_connsp_2(sK3,sK2,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5412])).

cnf(c_5421,plain,
    ( m1_connsp_2(sK3,sK2,sK0(k1_tops_1(sK2,sK3),X0)) = iProver_top
    | m1_subset_1(sK0(k1_tops_1(sK2,sK3),X0),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_tops_1(sK2,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_5413])).

cnf(c_13610,plain,
    ( m1_connsp_2(sK3,sK2,sK0(k1_tops_1(sK2,sK3),X0)) = iProver_top
    | r1_tarski(k1_tops_1(sK2,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12297,c_5421])).

cnf(c_13649,plain,
    ( r2_hidden(sK0(k1_tops_1(sK2,sK3),X0),sK3) = iProver_top
    | r1_tarski(k1_tops_1(sK2,sK3),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13608,c_13610])).

cnf(c_1413,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_27659,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_13649,c_1413])).

cnf(c_27691,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_27659])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1956,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | ~ r1_tarski(sK3,k1_tops_1(sK2,sK3))
    | k1_tops_1(sK2,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28327,c_27691,c_11102,c_1956,c_1892,c_36,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:32:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.79/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.79/1.51  
% 7.79/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.79/1.51  
% 7.79/1.51  ------  iProver source info
% 7.79/1.51  
% 7.79/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.79/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.79/1.51  git: non_committed_changes: false
% 7.79/1.51  git: last_make_outside_of_git: false
% 7.79/1.51  
% 7.79/1.51  ------ 
% 7.79/1.51  ------ Parsing...
% 7.79/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.79/1.51  
% 7.79/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.79/1.51  
% 7.79/1.51  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.79/1.51  
% 7.79/1.51  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.79/1.51  ------ Proving...
% 7.79/1.51  ------ Problem Properties 
% 7.79/1.51  
% 7.79/1.51  
% 7.79/1.51  clauses                                 36
% 7.79/1.51  conjectures                             10
% 7.79/1.51  EPR                                     9
% 7.79/1.51  Horn                                    21
% 7.79/1.51  unary                                   5
% 7.79/1.51  binary                                  8
% 7.79/1.51  lits                                    143
% 7.79/1.51  lits eq                                 3
% 7.79/1.51  fd_pure                                 0
% 7.79/1.51  fd_pseudo                               0
% 7.79/1.51  fd_cond                                 0
% 7.79/1.51  fd_pseudo_cond                          1
% 7.79/1.51  AC symbols                              0
% 7.79/1.51  
% 7.79/1.51  ------ Input Options Time Limit: Unbounded
% 7.79/1.51  
% 7.79/1.51  
% 7.79/1.51  ------ 
% 7.79/1.51  Current options:
% 7.79/1.51  ------ 
% 7.79/1.51  
% 7.79/1.51  
% 7.79/1.51  
% 7.79/1.51  
% 7.79/1.51  ------ Proving...
% 7.79/1.51  
% 7.79/1.51  
% 7.79/1.51  % SZS status Theorem for theBenchmark.p
% 7.79/1.51  
% 7.79/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.79/1.51  
% 7.79/1.51  fof(f4,axiom,(
% 7.79/1.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.79/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.51  
% 7.79/1.51  fof(f16,plain,(
% 7.79/1.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.79/1.51    inference(ennf_transformation,[],[f4])).
% 7.79/1.51  
% 7.79/1.51  fof(f17,plain,(
% 7.79/1.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.79/1.51    inference(flattening,[],[f16])).
% 7.79/1.51  
% 7.79/1.51  fof(f64,plain,(
% 7.79/1.51    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.79/1.51    inference(cnf_transformation,[],[f17])).
% 7.79/1.51  
% 7.79/1.51  fof(f10,axiom,(
% 7.79/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 7.79/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.51  
% 7.79/1.51  fof(f28,plain,(
% 7.79/1.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.79/1.51    inference(ennf_transformation,[],[f10])).
% 7.79/1.51  
% 7.79/1.51  fof(f29,plain,(
% 7.79/1.51    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.79/1.51    inference(flattening,[],[f28])).
% 7.79/1.51  
% 7.79/1.51  fof(f72,plain,(
% 7.79/1.51    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.79/1.51    inference(cnf_transformation,[],[f29])).
% 7.79/1.51  
% 7.79/1.51  fof(f13,conjecture,(
% 7.79/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 7.79/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.51  
% 7.79/1.51  fof(f14,negated_conjecture,(
% 7.79/1.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 7.79/1.51    inference(negated_conjecture,[],[f13])).
% 7.79/1.51  
% 7.79/1.51  fof(f34,plain,(
% 7.79/1.51    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.79/1.51    inference(ennf_transformation,[],[f14])).
% 7.79/1.51  
% 7.79/1.51  fof(f35,plain,(
% 7.79/1.51    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.79/1.51    inference(flattening,[],[f34])).
% 7.79/1.51  
% 7.79/1.51  fof(f48,plain,(
% 7.79/1.51    ? [X0] : (? [X1] : (((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.79/1.51    inference(nnf_transformation,[],[f35])).
% 7.79/1.51  
% 7.79/1.51  fof(f49,plain,(
% 7.79/1.51    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.79/1.51    inference(flattening,[],[f48])).
% 7.79/1.51  
% 7.79/1.51  fof(f50,plain,(
% 7.79/1.51    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.79/1.51    inference(rectify,[],[f49])).
% 7.79/1.51  
% 7.79/1.51  fof(f54,plain,(
% 7.79/1.51    ( ! [X0,X1] : (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK5(X4),X1) & m1_connsp_2(sK5(X4),X0,X4) & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 7.79/1.51    introduced(choice_axiom,[])).
% 7.79/1.51  
% 7.79/1.51  fof(f53,plain,(
% 7.79/1.51    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK4,X1) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 7.79/1.51    introduced(choice_axiom,[])).
% 7.79/1.51  
% 7.79/1.51  fof(f52,plain,(
% 7.79/1.51    ( ! [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(sK3,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,sK3) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.79/1.51    introduced(choice_axiom,[])).
% 7.79/1.51  
% 7.79/1.51  fof(f51,plain,(
% 7.79/1.51    ? [X0] : (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,sK2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) | ~v3_pre_topc(X1,sK2)) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,sK2,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(sK2))) | v3_pre_topc(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 7.79/1.51    introduced(choice_axiom,[])).
% 7.79/1.51  
% 7.79/1.51  fof(f55,plain,(
% 7.79/1.51    (((! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,sK2,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) | ~v3_pre_topc(sK3,sK2)) & (! [X4] : ((r1_tarski(sK5(X4),sK3) & m1_connsp_2(sK5(X4),sK2,X4) & m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2)))) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2))) | v3_pre_topc(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 7.79/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f50,f54,f53,f52,f51])).
% 7.79/1.51  
% 7.79/1.51  fof(f82,plain,(
% 7.79/1.51    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 7.79/1.51    inference(cnf_transformation,[],[f55])).
% 7.79/1.51  
% 7.79/1.51  fof(f80,plain,(
% 7.79/1.51    v2_pre_topc(sK2)),
% 7.79/1.51    inference(cnf_transformation,[],[f55])).
% 7.79/1.51  
% 7.79/1.51  fof(f81,plain,(
% 7.79/1.51    l1_pre_topc(sK2)),
% 7.79/1.51    inference(cnf_transformation,[],[f55])).
% 7.79/1.51  
% 7.79/1.51  fof(f8,axiom,(
% 7.79/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 7.79/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.51  
% 7.79/1.51  fof(f24,plain,(
% 7.79/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.79/1.51    inference(ennf_transformation,[],[f8])).
% 7.79/1.51  
% 7.79/1.51  fof(f25,plain,(
% 7.79/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.79/1.51    inference(flattening,[],[f24])).
% 7.79/1.51  
% 7.79/1.51  fof(f69,plain,(
% 7.79/1.51    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.79/1.51    inference(cnf_transformation,[],[f25])).
% 7.79/1.51  
% 7.79/1.51  fof(f68,plain,(
% 7.79/1.51    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.79/1.51    inference(cnf_transformation,[],[f25])).
% 7.79/1.51  
% 7.79/1.51  fof(f79,plain,(
% 7.79/1.51    ~v2_struct_0(sK2)),
% 7.79/1.51    inference(cnf_transformation,[],[f55])).
% 7.79/1.51  
% 7.79/1.51  fof(f88,plain,(
% 7.79/1.51    ( ! [X3] : (~r1_tarski(X3,sK3) | ~m1_connsp_2(X3,sK2,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(sK3,sK2)) )),
% 7.79/1.51    inference(cnf_transformation,[],[f55])).
% 7.79/1.51  
% 7.79/1.51  fof(f2,axiom,(
% 7.79/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.79/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.51  
% 7.79/1.51  fof(f40,plain,(
% 7.79/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.79/1.51    inference(nnf_transformation,[],[f2])).
% 7.79/1.51  
% 7.79/1.51  fof(f41,plain,(
% 7.79/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.79/1.51    inference(flattening,[],[f40])).
% 7.79/1.51  
% 7.79/1.51  fof(f59,plain,(
% 7.79/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.79/1.51    inference(cnf_transformation,[],[f41])).
% 7.79/1.51  
% 7.79/1.51  fof(f90,plain,(
% 7.79/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.79/1.51    inference(equality_resolution,[],[f59])).
% 7.79/1.51  
% 7.79/1.51  fof(f87,plain,(
% 7.79/1.51    r2_hidden(sK4,sK3) | ~v3_pre_topc(sK3,sK2)),
% 7.79/1.51    inference(cnf_transformation,[],[f55])).
% 7.79/1.51  
% 7.79/1.51  fof(f9,axiom,(
% 7.79/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 7.79/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.51  
% 7.79/1.51  fof(f26,plain,(
% 7.79/1.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.79/1.51    inference(ennf_transformation,[],[f9])).
% 7.79/1.51  
% 7.79/1.51  fof(f27,plain,(
% 7.79/1.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.79/1.51    inference(flattening,[],[f26])).
% 7.79/1.51  
% 7.79/1.51  fof(f43,plain,(
% 7.79/1.51    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.79/1.51    inference(nnf_transformation,[],[f27])).
% 7.79/1.51  
% 7.79/1.51  fof(f70,plain,(
% 7.79/1.51    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.79/1.51    inference(cnf_transformation,[],[f43])).
% 7.79/1.51  
% 7.79/1.51  fof(f83,plain,(
% 7.79/1.51    ( ! [X4] : (m1_subset_1(sK5(X4),k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2)) | v3_pre_topc(sK3,sK2)) )),
% 7.79/1.51    inference(cnf_transformation,[],[f55])).
% 7.79/1.51  
% 7.79/1.51  fof(f7,axiom,(
% 7.79/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 7.79/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.51  
% 7.79/1.51  fof(f22,plain,(
% 7.79/1.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.79/1.51    inference(ennf_transformation,[],[f7])).
% 7.79/1.51  
% 7.79/1.51  fof(f23,plain,(
% 7.79/1.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.79/1.51    inference(flattening,[],[f22])).
% 7.79/1.51  
% 7.79/1.51  fof(f67,plain,(
% 7.79/1.51    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.79/1.51    inference(cnf_transformation,[],[f23])).
% 7.79/1.51  
% 7.79/1.51  fof(f1,axiom,(
% 7.79/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.79/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.51  
% 7.79/1.51  fof(f15,plain,(
% 7.79/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.79/1.51    inference(ennf_transformation,[],[f1])).
% 7.79/1.51  
% 7.79/1.51  fof(f36,plain,(
% 7.79/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.79/1.51    inference(nnf_transformation,[],[f15])).
% 7.79/1.51  
% 7.79/1.51  fof(f37,plain,(
% 7.79/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.79/1.51    inference(rectify,[],[f36])).
% 7.79/1.51  
% 7.79/1.51  fof(f38,plain,(
% 7.79/1.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.79/1.51    introduced(choice_axiom,[])).
% 7.79/1.51  
% 7.79/1.51  fof(f39,plain,(
% 7.79/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.79/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 7.79/1.51  
% 7.79/1.51  fof(f56,plain,(
% 7.79/1.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.79/1.51    inference(cnf_transformation,[],[f39])).
% 7.79/1.51  
% 7.79/1.51  fof(f85,plain,(
% 7.79/1.51    ( ! [X4] : (r1_tarski(sK5(X4),sK3) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2)) | v3_pre_topc(sK3,sK2)) )),
% 7.79/1.51    inference(cnf_transformation,[],[f55])).
% 7.79/1.51  
% 7.79/1.51  fof(f84,plain,(
% 7.79/1.51    ( ! [X4] : (m1_connsp_2(sK5(X4),sK2,X4) | ~r2_hidden(X4,sK3) | ~m1_subset_1(X4,u1_struct_0(sK2)) | v3_pre_topc(sK3,sK2)) )),
% 7.79/1.51    inference(cnf_transformation,[],[f55])).
% 7.79/1.51  
% 7.79/1.51  fof(f58,plain,(
% 7.79/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.79/1.51    inference(cnf_transformation,[],[f39])).
% 7.79/1.51  
% 7.79/1.51  fof(f57,plain,(
% 7.79/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.79/1.51    inference(cnf_transformation,[],[f39])).
% 7.79/1.51  
% 7.79/1.51  fof(f5,axiom,(
% 7.79/1.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.79/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.51  
% 7.79/1.51  fof(f18,plain,(
% 7.79/1.51    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.79/1.51    inference(ennf_transformation,[],[f5])).
% 7.79/1.51  
% 7.79/1.51  fof(f19,plain,(
% 7.79/1.51    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.79/1.51    inference(flattening,[],[f18])).
% 7.79/1.51  
% 7.79/1.51  fof(f65,plain,(
% 7.79/1.51    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.79/1.51    inference(cnf_transformation,[],[f19])).
% 7.79/1.51  
% 7.79/1.51  fof(f11,axiom,(
% 7.79/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 7.79/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.51  
% 7.79/1.51  fof(f30,plain,(
% 7.79/1.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.79/1.51    inference(ennf_transformation,[],[f11])).
% 7.79/1.51  
% 7.79/1.51  fof(f31,plain,(
% 7.79/1.51    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.79/1.51    inference(flattening,[],[f30])).
% 7.79/1.51  
% 7.79/1.51  fof(f73,plain,(
% 7.79/1.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.79/1.51    inference(cnf_transformation,[],[f31])).
% 7.79/1.51  
% 7.79/1.51  fof(f71,plain,(
% 7.79/1.51    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.79/1.51    inference(cnf_transformation,[],[f43])).
% 7.79/1.51  
% 7.79/1.51  fof(f61,plain,(
% 7.79/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.79/1.51    inference(cnf_transformation,[],[f41])).
% 7.79/1.51  
% 7.79/1.51  cnf(c_8,plain,
% 7.79/1.51      ( m1_subset_1(X0,X1)
% 7.79/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.79/1.51      | ~ r2_hidden(X0,X2) ),
% 7.79/1.51      inference(cnf_transformation,[],[f64]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_16,plain,
% 7.79/1.51      ( m1_connsp_2(X0,X1,X2)
% 7.79/1.51      | ~ v3_pre_topc(X0,X1)
% 7.79/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.79/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | ~ r2_hidden(X2,X0)
% 7.79/1.51      | v2_struct_0(X1)
% 7.79/1.51      | ~ v2_pre_topc(X1)
% 7.79/1.51      | ~ l1_pre_topc(X1) ),
% 7.79/1.51      inference(cnf_transformation,[],[f72]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_2365,plain,
% 7.79/1.51      ( m1_connsp_2(X0,X1,X2)
% 7.79/1.51      | ~ v3_pre_topc(X0,X1)
% 7.79/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | ~ r2_hidden(X2,X0)
% 7.79/1.51      | v2_struct_0(X1)
% 7.79/1.51      | ~ v2_pre_topc(X1)
% 7.79/1.51      | ~ l1_pre_topc(X1) ),
% 7.79/1.51      inference(backward_subsumption_resolution,[status(thm)],[c_8,c_16]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_29,negated_conjecture,
% 7.79/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.79/1.51      inference(cnf_transformation,[],[f82]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_14362,plain,
% 7.79/1.51      ( m1_connsp_2(sK3,sK2,X0)
% 7.79/1.51      | ~ v3_pre_topc(sK3,sK2)
% 7.79/1.51      | ~ r2_hidden(X0,sK3)
% 7.79/1.51      | v2_struct_0(sK2)
% 7.79/1.51      | ~ v2_pre_topc(sK2)
% 7.79/1.51      | ~ l1_pre_topc(sK2) ),
% 7.79/1.51      inference(resolution,[status(thm)],[c_2365,c_29]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_31,negated_conjecture,
% 7.79/1.51      ( v2_pre_topc(sK2) ),
% 7.79/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_34,plain,
% 7.79/1.51      ( v2_pre_topc(sK2) = iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_30,negated_conjecture,
% 7.79/1.51      ( l1_pre_topc(sK2) ),
% 7.79/1.51      inference(cnf_transformation,[],[f81]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_35,plain,
% 7.79/1.51      ( l1_pre_topc(sK2) = iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_36,plain,
% 7.79/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_12,plain,
% 7.79/1.51      ( v3_pre_topc(X0,X1)
% 7.79/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.79/1.51      | ~ v2_pre_topc(X1)
% 7.79/1.51      | ~ l1_pre_topc(X1)
% 7.79/1.51      | ~ l1_pre_topc(X3)
% 7.79/1.51      | k1_tops_1(X1,X0) != X0 ),
% 7.79/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_586,plain,
% 7.79/1.51      ( v3_pre_topc(X0,X1)
% 7.79/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | ~ v2_pre_topc(X1)
% 7.79/1.51      | ~ l1_pre_topc(X1)
% 7.79/1.51      | k1_tops_1(X1,X0) != X0
% 7.79/1.51      | ~ sP3_iProver_split ),
% 7.79/1.51      inference(splitting,
% 7.79/1.51                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 7.79/1.51                [c_12]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_587,plain,
% 7.79/1.51      ( sP3_iProver_split | sP2_iProver_split ),
% 7.79/1.51      inference(splitting,
% 7.79/1.51                [splitting(split),new_symbols(definition,[])],
% 7.79/1.51                [c_12]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_585,plain,
% 7.79/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | ~ l1_pre_topc(X1)
% 7.79/1.51      | ~ sP2_iProver_split ),
% 7.79/1.51      inference(splitting,
% 7.79/1.51                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 7.79/1.51                [c_12]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_914,plain,
% 7.79/1.51      ( k1_tops_1(X1,X0) != X0
% 7.79/1.51      | ~ l1_pre_topc(X1)
% 7.79/1.51      | ~ v2_pre_topc(X1)
% 7.79/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | v3_pre_topc(X0,X1) ),
% 7.79/1.51      inference(global_propositional_subsumption,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_586,c_587,c_585]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_915,plain,
% 7.79/1.51      ( v3_pre_topc(X0,X1)
% 7.79/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | ~ v2_pre_topc(X1)
% 7.79/1.51      | ~ l1_pre_topc(X1)
% 7.79/1.51      | k1_tops_1(X1,X0) != X0 ),
% 7.79/1.51      inference(renaming,[status(thm)],[c_914]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1891,plain,
% 7.79/1.51      ( v3_pre_topc(sK3,sK2)
% 7.79/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.79/1.51      | ~ v2_pre_topc(sK2)
% 7.79/1.51      | ~ l1_pre_topc(sK2)
% 7.79/1.51      | k1_tops_1(sK2,sK3) != sK3 ),
% 7.79/1.51      inference(instantiation,[status(thm)],[c_915]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1892,plain,
% 7.79/1.51      ( k1_tops_1(sK2,sK3) != sK3
% 7.79/1.51      | v3_pre_topc(sK3,sK2) = iProver_top
% 7.79/1.51      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.79/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.79/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_1891]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1381,plain,
% 7.79/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_13,plain,
% 7.79/1.51      ( ~ v3_pre_topc(X0,X1)
% 7.79/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.79/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | ~ v2_pre_topc(X3)
% 7.79/1.51      | ~ l1_pre_topc(X3)
% 7.79/1.51      | ~ l1_pre_topc(X1)
% 7.79/1.51      | k1_tops_1(X1,X0) = X0 ),
% 7.79/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_583,plain,
% 7.79/1.51      ( ~ v3_pre_topc(X0,X1)
% 7.79/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | ~ l1_pre_topc(X1)
% 7.79/1.51      | k1_tops_1(X1,X0) = X0
% 7.79/1.51      | ~ sP1_iProver_split ),
% 7.79/1.51      inference(splitting,
% 7.79/1.51                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 7.79/1.51                [c_13]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1398,plain,
% 7.79/1.51      ( k1_tops_1(X0,X1) = X1
% 7.79/1.51      | v3_pre_topc(X1,X0) != iProver_top
% 7.79/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.79/1.51      | l1_pre_topc(X0) != iProver_top
% 7.79/1.51      | sP1_iProver_split != iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_584,plain,
% 7.79/1.51      ( sP1_iProver_split | sP0_iProver_split ),
% 7.79/1.51      inference(splitting,
% 7.79/1.51                [splitting(split),new_symbols(definition,[])],
% 7.79/1.51                [c_13]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_632,plain,
% 7.79/1.51      ( sP1_iProver_split = iProver_top
% 7.79/1.51      | sP0_iProver_split = iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_584]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_633,plain,
% 7.79/1.51      ( k1_tops_1(X0,X1) = X1
% 7.79/1.51      | v3_pre_topc(X1,X0) != iProver_top
% 7.79/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.79/1.51      | l1_pre_topc(X0) != iProver_top
% 7.79/1.51      | sP1_iProver_split != iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_582,plain,
% 7.79/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | ~ v2_pre_topc(X1)
% 7.79/1.51      | ~ l1_pre_topc(X1)
% 7.79/1.51      | ~ sP0_iProver_split ),
% 7.79/1.51      inference(splitting,
% 7.79/1.51                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.79/1.51                [c_13]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_2382,plain,
% 7.79/1.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.79/1.51      | ~ v2_pre_topc(sK2)
% 7.79/1.51      | ~ l1_pre_topc(sK2)
% 7.79/1.51      | ~ sP0_iProver_split ),
% 7.79/1.51      inference(instantiation,[status(thm)],[c_582]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_2383,plain,
% 7.79/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.79/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.79/1.51      | l1_pre_topc(sK2) != iProver_top
% 7.79/1.51      | sP0_iProver_split != iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_2382]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_5940,plain,
% 7.79/1.51      ( l1_pre_topc(X0) != iProver_top
% 7.79/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.79/1.51      | v3_pre_topc(X1,X0) != iProver_top
% 7.79/1.51      | k1_tops_1(X0,X1) = X1 ),
% 7.79/1.51      inference(global_propositional_subsumption,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_1398,c_34,c_35,c_36,c_632,c_633,c_2383]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_5941,plain,
% 7.79/1.51      ( k1_tops_1(X0,X1) = X1
% 7.79/1.51      | v3_pre_topc(X1,X0) != iProver_top
% 7.79/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.79/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.79/1.51      inference(renaming,[status(thm)],[c_5940]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_5954,plain,
% 7.79/1.51      ( k1_tops_1(sK2,sK3) = sK3
% 7.79/1.51      | v3_pre_topc(sK3,sK2) != iProver_top
% 7.79/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.79/1.51      inference(superposition,[status(thm)],[c_1381,c_5941]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_6306,plain,
% 7.79/1.51      ( v3_pre_topc(sK3,sK2) != iProver_top | k1_tops_1(sK2,sK3) = sK3 ),
% 7.79/1.51      inference(global_propositional_subsumption,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_5954,c_34,c_35,c_36,c_632,c_2383,c_5571]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_6307,plain,
% 7.79/1.51      ( k1_tops_1(sK2,sK3) = sK3 | v3_pre_topc(sK3,sK2) != iProver_top ),
% 7.79/1.51      inference(renaming,[status(thm)],[c_6306]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_6308,plain,
% 7.79/1.51      ( ~ v3_pre_topc(sK3,sK2) | k1_tops_1(sK2,sK3) = sK3 ),
% 7.79/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_6307]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1394,plain,
% 7.79/1.51      ( m1_connsp_2(X0,X1,X2) = iProver_top
% 7.79/1.51      | v3_pre_topc(X0,X1) != iProver_top
% 7.79/1.51      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 7.79/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.79/1.51      | r2_hidden(X2,X0) != iProver_top
% 7.79/1.51      | v2_struct_0(X1) = iProver_top
% 7.79/1.51      | v2_pre_topc(X1) != iProver_top
% 7.79/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1406,plain,
% 7.79/1.51      ( m1_subset_1(X0,X1) = iProver_top
% 7.79/1.51      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.79/1.51      | r2_hidden(X0,X2) != iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1672,plain,
% 7.79/1.51      ( m1_connsp_2(X0,X1,X2) = iProver_top
% 7.79/1.51      | v3_pre_topc(X0,X1) != iProver_top
% 7.79/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.79/1.51      | r2_hidden(X2,X0) != iProver_top
% 7.79/1.51      | v2_struct_0(X1) = iProver_top
% 7.79/1.51      | v2_pre_topc(X1) != iProver_top
% 7.79/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.79/1.51      inference(forward_subsumption_resolution,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_1394,c_1406]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_10456,plain,
% 7.79/1.51      ( m1_connsp_2(sK3,sK2,X0) = iProver_top
% 7.79/1.51      | v3_pre_topc(sK3,sK2) != iProver_top
% 7.79/1.51      | r2_hidden(X0,sK3) != iProver_top
% 7.79/1.51      | v2_struct_0(sK2) = iProver_top
% 7.79/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.79/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.79/1.51      inference(superposition,[status(thm)],[c_1381,c_1672]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_32,negated_conjecture,
% 7.79/1.51      ( ~ v2_struct_0(sK2) ),
% 7.79/1.51      inference(cnf_transformation,[],[f79]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_33,plain,
% 7.79/1.51      ( v2_struct_0(sK2) != iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_10908,plain,
% 7.79/1.51      ( r2_hidden(X0,sK3) != iProver_top
% 7.79/1.51      | v3_pre_topc(sK3,sK2) != iProver_top
% 7.79/1.51      | m1_connsp_2(sK3,sK2,X0) = iProver_top ),
% 7.79/1.51      inference(global_propositional_subsumption,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_10456,c_33,c_34,c_35]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_10909,plain,
% 7.79/1.51      ( m1_connsp_2(sK3,sK2,X0) = iProver_top
% 7.79/1.51      | v3_pre_topc(sK3,sK2) != iProver_top
% 7.79/1.51      | r2_hidden(X0,sK3) != iProver_top ),
% 7.79/1.51      inference(renaming,[status(thm)],[c_10908]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_23,negated_conjecture,
% 7.79/1.51      ( ~ m1_connsp_2(X0,sK2,sK4)
% 7.79/1.51      | ~ v3_pre_topc(sK3,sK2)
% 7.79/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.79/1.51      | ~ r1_tarski(X0,sK3) ),
% 7.79/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1387,plain,
% 7.79/1.51      ( m1_connsp_2(X0,sK2,sK4) != iProver_top
% 7.79/1.51      | v3_pre_topc(sK3,sK2) != iProver_top
% 7.79/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.79/1.51      | r1_tarski(X0,sK3) != iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1905,plain,
% 7.79/1.51      ( m1_connsp_2(sK3,sK2,sK4) != iProver_top
% 7.79/1.51      | v3_pre_topc(sK3,sK2) != iProver_top
% 7.79/1.51      | r1_tarski(sK3,sK3) != iProver_top ),
% 7.79/1.51      inference(superposition,[status(thm)],[c_1381,c_1387]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_5,plain,
% 7.79/1.51      ( r1_tarski(X0,X0) ),
% 7.79/1.51      inference(cnf_transformation,[],[f90]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_2218,plain,
% 7.79/1.51      ( r1_tarski(sK3,sK3) ),
% 7.79/1.51      inference(instantiation,[status(thm)],[c_5]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_2219,plain,
% 7.79/1.51      ( r1_tarski(sK3,sK3) = iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_2218]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_2333,plain,
% 7.79/1.51      ( v3_pre_topc(sK3,sK2) != iProver_top
% 7.79/1.51      | m1_connsp_2(sK3,sK2,sK4) != iProver_top ),
% 7.79/1.51      inference(global_propositional_subsumption,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_1905,c_2219]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_2334,plain,
% 7.79/1.51      ( m1_connsp_2(sK3,sK2,sK4) != iProver_top
% 7.79/1.51      | v3_pre_topc(sK3,sK2) != iProver_top ),
% 7.79/1.51      inference(renaming,[status(thm)],[c_2333]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_10918,plain,
% 7.79/1.51      ( v3_pre_topc(sK3,sK2) != iProver_top
% 7.79/1.51      | r2_hidden(sK4,sK3) != iProver_top ),
% 7.79/1.51      inference(superposition,[status(thm)],[c_10909,c_2334]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_24,negated_conjecture,
% 7.79/1.51      ( ~ v3_pre_topc(sK3,sK2) | r2_hidden(sK4,sK3) ),
% 7.79/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_47,plain,
% 7.79/1.51      ( v3_pre_topc(sK3,sK2) != iProver_top
% 7.79/1.51      | r2_hidden(sK4,sK3) = iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_11102,plain,
% 7.79/1.51      ( v3_pre_topc(sK3,sK2) != iProver_top ),
% 7.79/1.51      inference(global_propositional_subsumption,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_10918,c_47]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_14862,plain,
% 7.79/1.51      ( ~ v3_pre_topc(sK3,sK2) ),
% 7.79/1.51      inference(global_propositional_subsumption,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_14362,c_34,c_35,c_36,c_47,c_1892,c_6308,c_10918]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_15,plain,
% 7.79/1.51      ( ~ m1_connsp_2(X0,X1,X2)
% 7.79/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.79/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | r2_hidden(X2,k1_tops_1(X1,X0))
% 7.79/1.51      | v2_struct_0(X1)
% 7.79/1.51      | ~ v2_pre_topc(X1)
% 7.79/1.51      | ~ l1_pre_topc(X1) ),
% 7.79/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_2375,plain,
% 7.79/1.51      ( m1_subset_1(X0,u1_struct_0(sK2)) | ~ r2_hidden(X0,sK3) ),
% 7.79/1.51      inference(resolution,[status(thm)],[c_8,c_29]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_28,negated_conjecture,
% 7.79/1.51      ( v3_pre_topc(sK3,sK2)
% 7.79/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.79/1.51      | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.79/1.51      | ~ r2_hidden(X0,sK3) ),
% 7.79/1.51      inference(cnf_transformation,[],[f83]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_2483,plain,
% 7.79/1.51      ( v3_pre_topc(sK3,sK2)
% 7.79/1.51      | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.79/1.51      | ~ r2_hidden(X0,sK3) ),
% 7.79/1.51      inference(backward_subsumption_resolution,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_2375,c_28]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_5370,plain,
% 7.79/1.51      ( ~ m1_connsp_2(sK5(X0),sK2,X1)
% 7.79/1.51      | v3_pre_topc(sK3,sK2)
% 7.79/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.79/1.51      | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
% 7.79/1.51      | ~ r2_hidden(X0,sK3)
% 7.79/1.51      | v2_struct_0(sK2)
% 7.79/1.51      | ~ v2_pre_topc(sK2)
% 7.79/1.51      | ~ l1_pre_topc(sK2) ),
% 7.79/1.51      inference(resolution,[status(thm)],[c_15,c_2483]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1382,plain,
% 7.79/1.51      ( v3_pre_topc(sK3,sK2) = iProver_top
% 7.79/1.51      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.79/1.51      | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 7.79/1.51      | r2_hidden(X0,sK3) != iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1395,plain,
% 7.79/1.51      ( m1_connsp_2(X0,X1,X2) != iProver_top
% 7.79/1.51      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 7.79/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.79/1.51      | r2_hidden(X2,k1_tops_1(X1,X0)) = iProver_top
% 7.79/1.51      | v2_struct_0(X1) = iProver_top
% 7.79/1.51      | v2_pre_topc(X1) != iProver_top
% 7.79/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_4910,plain,
% 7.79/1.51      ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
% 7.79/1.51      | v3_pre_topc(sK3,sK2) = iProver_top
% 7.79/1.51      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.79/1.51      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 7.79/1.51      | r2_hidden(X1,k1_tops_1(sK2,sK5(X0))) = iProver_top
% 7.79/1.51      | r2_hidden(X0,sK3) != iProver_top
% 7.79/1.51      | v2_struct_0(sK2) = iProver_top
% 7.79/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.79/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.79/1.51      inference(superposition,[status(thm)],[c_1382,c_1395]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_5371,plain,
% 7.79/1.51      ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
% 7.79/1.51      | v3_pre_topc(sK3,sK2) = iProver_top
% 7.79/1.51      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 7.79/1.51      | r2_hidden(X1,k1_tops_1(sK2,sK5(X0))) = iProver_top
% 7.79/1.51      | r2_hidden(X0,sK3) != iProver_top
% 7.79/1.51      | v2_struct_0(sK2) = iProver_top
% 7.79/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.79/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_5370]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_5433,plain,
% 7.79/1.51      ( r2_hidden(X0,sK3) != iProver_top
% 7.79/1.51      | r2_hidden(X1,k1_tops_1(sK2,sK5(X0))) = iProver_top
% 7.79/1.51      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 7.79/1.51      | m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
% 7.79/1.51      | v3_pre_topc(sK3,sK2) = iProver_top ),
% 7.79/1.51      inference(global_propositional_subsumption,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_4910,c_33,c_34,c_35,c_5371]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_5434,plain,
% 7.79/1.51      ( m1_connsp_2(sK5(X0),sK2,X1) != iProver_top
% 7.79/1.51      | v3_pre_topc(sK3,sK2) = iProver_top
% 7.79/1.51      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 7.79/1.51      | r2_hidden(X1,k1_tops_1(sK2,sK5(X0))) = iProver_top
% 7.79/1.51      | r2_hidden(X0,sK3) != iProver_top ),
% 7.79/1.51      inference(renaming,[status(thm)],[c_5433]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_5435,plain,
% 7.79/1.51      ( ~ m1_connsp_2(sK5(X0),sK2,X1)
% 7.79/1.51      | v3_pre_topc(sK3,sK2)
% 7.79/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.79/1.51      | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
% 7.79/1.51      | ~ r2_hidden(X0,sK3) ),
% 7.79/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_5434]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_5734,plain,
% 7.79/1.51      ( ~ r2_hidden(X0,sK3)
% 7.79/1.51      | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
% 7.79/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.79/1.51      | v3_pre_topc(sK3,sK2)
% 7.79/1.51      | ~ m1_connsp_2(sK5(X0),sK2,X1) ),
% 7.79/1.51      inference(global_propositional_subsumption,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_5370,c_5435]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_5735,plain,
% 7.79/1.51      ( ~ m1_connsp_2(sK5(X0),sK2,X1)
% 7.79/1.51      | v3_pre_topc(sK3,sK2)
% 7.79/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.79/1.51      | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
% 7.79/1.51      | ~ r2_hidden(X0,sK3) ),
% 7.79/1.51      inference(renaming,[status(thm)],[c_5734]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_14905,plain,
% 7.79/1.51      ( ~ m1_connsp_2(sK5(X0),sK2,X1)
% 7.79/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.79/1.51      | r2_hidden(X1,k1_tops_1(sK2,sK5(X0)))
% 7.79/1.51      | ~ r2_hidden(X0,sK3) ),
% 7.79/1.51      inference(backward_subsumption_resolution,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_14862,c_5735]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_11,plain,
% 7.79/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | ~ r1_tarski(X0,X2)
% 7.79/1.51      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 7.79/1.51      | ~ l1_pre_topc(X1) ),
% 7.79/1.51      inference(cnf_transformation,[],[f67]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_2,plain,
% 7.79/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.79/1.51      inference(cnf_transformation,[],[f56]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_4000,plain,
% 7.79/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | ~ r2_hidden(X3,k1_tops_1(X1,X0))
% 7.79/1.51      | r2_hidden(X3,k1_tops_1(X1,X2))
% 7.79/1.51      | ~ r1_tarski(X0,X2)
% 7.79/1.51      | ~ l1_pre_topc(X1) ),
% 7.79/1.51      inference(resolution,[status(thm)],[c_11,c_2]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_16942,plain,
% 7.79/1.51      ( ~ m1_connsp_2(sK5(X0),sK2,X1)
% 7.79/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.79/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.79/1.51      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.79/1.51      | r2_hidden(X1,k1_tops_1(sK2,X2))
% 7.79/1.51      | ~ r2_hidden(X0,sK3)
% 7.79/1.51      | ~ r1_tarski(sK5(X0),X2)
% 7.79/1.51      | ~ l1_pre_topc(sK2) ),
% 7.79/1.51      inference(resolution,[status(thm)],[c_14905,c_4000]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_14900,plain,
% 7.79/1.51      ( m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.79/1.51      | ~ r2_hidden(X0,sK3) ),
% 7.79/1.51      inference(backward_subsumption_resolution,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_14862,c_2483]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_25938,plain,
% 7.79/1.51      ( ~ r1_tarski(sK5(X0),X2)
% 7.79/1.51      | ~ r2_hidden(X0,sK3)
% 7.79/1.51      | r2_hidden(X1,k1_tops_1(sK2,X2))
% 7.79/1.51      | ~ m1_connsp_2(sK5(X0),sK2,X1)
% 7.79/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.79/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.79/1.51      inference(global_propositional_subsumption,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_16942,c_34,c_30,c_35,c_36,c_47,c_1892,c_2483,c_6308,
% 7.79/1.51                 c_6634,c_10918]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_25939,plain,
% 7.79/1.51      ( ~ m1_connsp_2(sK5(X0),sK2,X1)
% 7.79/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.79/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.79/1.51      | r2_hidden(X1,k1_tops_1(sK2,X2))
% 7.79/1.51      | ~ r2_hidden(X0,sK3)
% 7.79/1.51      | ~ r1_tarski(sK5(X0),X2) ),
% 7.79/1.51      inference(renaming,[status(thm)],[c_25938]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_25990,plain,
% 7.79/1.51      ( ~ m1_connsp_2(sK5(X0),sK2,X1)
% 7.79/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.79/1.51      | r2_hidden(X1,k1_tops_1(sK2,sK3))
% 7.79/1.51      | ~ r2_hidden(X0,sK3)
% 7.79/1.51      | ~ r1_tarski(sK5(X0),sK3) ),
% 7.79/1.51      inference(resolution,[status(thm)],[c_25939,c_29]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_26,negated_conjecture,
% 7.79/1.51      ( v3_pre_topc(sK3,sK2)
% 7.79/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.79/1.51      | ~ r2_hidden(X0,sK3)
% 7.79/1.51      | r1_tarski(sK5(X0),sK3) ),
% 7.79/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_2481,plain,
% 7.79/1.51      ( v3_pre_topc(sK3,sK2)
% 7.79/1.51      | ~ r2_hidden(X0,sK3)
% 7.79/1.51      | r1_tarski(sK5(X0),sK3) ),
% 7.79/1.51      inference(backward_subsumption_resolution,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_2375,c_26]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_25999,plain,
% 7.79/1.51      ( ~ r2_hidden(X0,sK3)
% 7.79/1.51      | r2_hidden(X1,k1_tops_1(sK2,sK3))
% 7.79/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.79/1.51      | ~ m1_connsp_2(sK5(X0),sK2,X1) ),
% 7.79/1.51      inference(global_propositional_subsumption,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_25990,c_34,c_35,c_36,c_47,c_1892,c_2481,c_6308,
% 7.79/1.51                 c_10918]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_26000,plain,
% 7.79/1.51      ( ~ m1_connsp_2(sK5(X0),sK2,X1)
% 7.79/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 7.79/1.51      | r2_hidden(X1,k1_tops_1(sK2,sK3))
% 7.79/1.51      | ~ r2_hidden(X0,sK3) ),
% 7.79/1.51      inference(renaming,[status(thm)],[c_25999]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_27,negated_conjecture,
% 7.79/1.51      ( m1_connsp_2(sK5(X0),sK2,X0)
% 7.79/1.51      | v3_pre_topc(sK3,sK2)
% 7.79/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.79/1.51      | ~ r2_hidden(X0,sK3) ),
% 7.79/1.51      inference(cnf_transformation,[],[f84]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_2482,plain,
% 7.79/1.51      ( m1_connsp_2(sK5(X0),sK2,X0)
% 7.79/1.51      | v3_pre_topc(sK3,sK2)
% 7.79/1.51      | ~ r2_hidden(X0,sK3) ),
% 7.79/1.51      inference(backward_subsumption_resolution,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_2375,c_27]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_14881,plain,
% 7.79/1.51      ( m1_connsp_2(sK5(X0),sK2,X0) | ~ r2_hidden(X0,sK3) ),
% 7.79/1.51      inference(backward_subsumption_resolution,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_14862,c_2482]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_26195,plain,
% 7.79/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 7.79/1.51      | r2_hidden(X0,k1_tops_1(sK2,sK3))
% 7.79/1.51      | ~ r2_hidden(X0,sK3) ),
% 7.79/1.51      inference(resolution,[status(thm)],[c_26000,c_14881]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_26208,plain,
% 7.79/1.51      ( r2_hidden(X0,k1_tops_1(sK2,sK3)) | ~ r2_hidden(X0,sK3) ),
% 7.79/1.51      inference(global_propositional_subsumption,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_26195,c_2375]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_0,plain,
% 7.79/1.51      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.79/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_27078,plain,
% 7.79/1.51      ( ~ r2_hidden(sK0(X0,k1_tops_1(sK2,sK3)),sK3)
% 7.79/1.51      | r1_tarski(X0,k1_tops_1(sK2,sK3)) ),
% 7.79/1.51      inference(resolution,[status(thm)],[c_26208,c_0]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1,plain,
% 7.79/1.51      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.79/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_28327,plain,
% 7.79/1.51      ( r1_tarski(sK3,k1_tops_1(sK2,sK3)) ),
% 7.79/1.51      inference(resolution,[status(thm)],[c_27078,c_1]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1412,plain,
% 7.79/1.51      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.79/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_9,plain,
% 7.79/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | ~ l1_pre_topc(X1) ),
% 7.79/1.51      inference(cnf_transformation,[],[f65]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1405,plain,
% 7.79/1.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.79/1.51      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.79/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_3417,plain,
% 7.79/1.51      ( m1_subset_1(X0,u1_struct_0(X1)) = iProver_top
% 7.79/1.51      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.79/1.51      | r2_hidden(X0,k1_tops_1(X1,X2)) != iProver_top
% 7.79/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.79/1.51      inference(superposition,[status(thm)],[c_1405,c_1406]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_12117,plain,
% 7.79/1.51      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 7.79/1.51      | r2_hidden(X0,k1_tops_1(sK2,sK3)) != iProver_top
% 7.79/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.79/1.51      inference(superposition,[status(thm)],[c_1381,c_3417]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_12289,plain,
% 7.79/1.51      ( r2_hidden(X0,k1_tops_1(sK2,sK3)) != iProver_top
% 7.79/1.51      | m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top ),
% 7.79/1.51      inference(global_propositional_subsumption,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_12117,c_35]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_12290,plain,
% 7.79/1.51      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 7.79/1.51      | r2_hidden(X0,k1_tops_1(sK2,sK3)) != iProver_top ),
% 7.79/1.51      inference(renaming,[status(thm)],[c_12289]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_12297,plain,
% 7.79/1.51      ( m1_subset_1(sK0(k1_tops_1(sK2,sK3),X0),u1_struct_0(sK2)) = iProver_top
% 7.79/1.51      | r1_tarski(k1_tops_1(sK2,sK3),X0) = iProver_top ),
% 7.79/1.51      inference(superposition,[status(thm)],[c_1412,c_12290]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_17,plain,
% 7.79/1.51      ( ~ m1_connsp_2(X0,X1,X2)
% 7.79/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.79/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | r2_hidden(X2,X0)
% 7.79/1.51      | v2_struct_0(X1)
% 7.79/1.51      | ~ v2_pre_topc(X1)
% 7.79/1.51      | ~ l1_pre_topc(X1) ),
% 7.79/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1393,plain,
% 7.79/1.51      ( m1_connsp_2(X0,X1,X2) != iProver_top
% 7.79/1.51      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 7.79/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.79/1.51      | r2_hidden(X2,X0) = iProver_top
% 7.79/1.51      | v2_struct_0(X1) = iProver_top
% 7.79/1.51      | v2_pre_topc(X1) != iProver_top
% 7.79/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_3645,plain,
% 7.79/1.51      ( m1_connsp_2(sK3,sK2,X0) != iProver_top
% 7.79/1.51      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.79/1.51      | r2_hidden(X0,sK3) = iProver_top
% 7.79/1.51      | v2_struct_0(sK2) = iProver_top
% 7.79/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.79/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.79/1.51      inference(superposition,[status(thm)],[c_1381,c_1393]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_4130,plain,
% 7.79/1.51      ( r2_hidden(X0,sK3) = iProver_top
% 7.79/1.51      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.79/1.51      | m1_connsp_2(sK3,sK2,X0) != iProver_top ),
% 7.79/1.51      inference(global_propositional_subsumption,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_3645,c_33,c_34,c_35]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_4131,plain,
% 7.79/1.51      ( m1_connsp_2(sK3,sK2,X0) != iProver_top
% 7.79/1.51      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.79/1.51      | r2_hidden(X0,sK3) = iProver_top ),
% 7.79/1.51      inference(renaming,[status(thm)],[c_4130]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_13608,plain,
% 7.79/1.51      ( m1_connsp_2(sK3,sK2,sK0(k1_tops_1(sK2,sK3),X0)) != iProver_top
% 7.79/1.51      | r2_hidden(sK0(k1_tops_1(sK2,sK3),X0),sK3) = iProver_top
% 7.79/1.51      | r1_tarski(k1_tops_1(sK2,sK3),X0) = iProver_top ),
% 7.79/1.51      inference(superposition,[status(thm)],[c_12297,c_4131]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_14,plain,
% 7.79/1.51      ( m1_connsp_2(X0,X1,X2)
% 7.79/1.51      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.79/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.79/1.51      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 7.79/1.51      | v2_struct_0(X1)
% 7.79/1.51      | ~ v2_pre_topc(X1)
% 7.79/1.51      | ~ l1_pre_topc(X1) ),
% 7.79/1.51      inference(cnf_transformation,[],[f71]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1396,plain,
% 7.79/1.51      ( m1_connsp_2(X0,X1,X2) = iProver_top
% 7.79/1.51      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 7.79/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.79/1.51      | r2_hidden(X2,k1_tops_1(X1,X0)) != iProver_top
% 7.79/1.51      | v2_struct_0(X1) = iProver_top
% 7.79/1.51      | v2_pre_topc(X1) != iProver_top
% 7.79/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_5113,plain,
% 7.79/1.51      ( m1_connsp_2(sK3,sK2,X0) = iProver_top
% 7.79/1.51      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.79/1.51      | r2_hidden(X0,k1_tops_1(sK2,sK3)) != iProver_top
% 7.79/1.51      | v2_struct_0(sK2) = iProver_top
% 7.79/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.79/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.79/1.51      inference(superposition,[status(thm)],[c_1381,c_1396]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_5412,plain,
% 7.79/1.51      ( r2_hidden(X0,k1_tops_1(sK2,sK3)) != iProver_top
% 7.79/1.51      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.79/1.51      | m1_connsp_2(sK3,sK2,X0) = iProver_top ),
% 7.79/1.51      inference(global_propositional_subsumption,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_5113,c_33,c_34,c_35]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_5413,plain,
% 7.79/1.51      ( m1_connsp_2(sK3,sK2,X0) = iProver_top
% 7.79/1.51      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 7.79/1.51      | r2_hidden(X0,k1_tops_1(sK2,sK3)) != iProver_top ),
% 7.79/1.51      inference(renaming,[status(thm)],[c_5412]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_5421,plain,
% 7.79/1.51      ( m1_connsp_2(sK3,sK2,sK0(k1_tops_1(sK2,sK3),X0)) = iProver_top
% 7.79/1.51      | m1_subset_1(sK0(k1_tops_1(sK2,sK3),X0),u1_struct_0(sK2)) != iProver_top
% 7.79/1.51      | r1_tarski(k1_tops_1(sK2,sK3),X0) = iProver_top ),
% 7.79/1.51      inference(superposition,[status(thm)],[c_1412,c_5413]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_13610,plain,
% 7.79/1.51      ( m1_connsp_2(sK3,sK2,sK0(k1_tops_1(sK2,sK3),X0)) = iProver_top
% 7.79/1.51      | r1_tarski(k1_tops_1(sK2,sK3),X0) = iProver_top ),
% 7.79/1.51      inference(superposition,[status(thm)],[c_12297,c_5421]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_13649,plain,
% 7.79/1.51      ( r2_hidden(sK0(k1_tops_1(sK2,sK3),X0),sK3) = iProver_top
% 7.79/1.51      | r1_tarski(k1_tops_1(sK2,sK3),X0) = iProver_top ),
% 7.79/1.51      inference(forward_subsumption_resolution,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_13608,c_13610]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1413,plain,
% 7.79/1.51      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.79/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.79/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_27659,plain,
% 7.79/1.51      ( r1_tarski(k1_tops_1(sK2,sK3),sK3) = iProver_top ),
% 7.79/1.51      inference(superposition,[status(thm)],[c_13649,c_1413]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_27691,plain,
% 7.79/1.51      ( r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
% 7.79/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_27659]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_3,plain,
% 7.79/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.79/1.51      inference(cnf_transformation,[],[f61]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(c_1956,plain,
% 7.79/1.51      ( ~ r1_tarski(k1_tops_1(sK2,sK3),sK3)
% 7.79/1.51      | ~ r1_tarski(sK3,k1_tops_1(sK2,sK3))
% 7.79/1.51      | k1_tops_1(sK2,sK3) = sK3 ),
% 7.79/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 7.79/1.51  
% 7.79/1.51  cnf(contradiction,plain,
% 7.79/1.51      ( $false ),
% 7.79/1.51      inference(minisat,
% 7.79/1.51                [status(thm)],
% 7.79/1.51                [c_28327,c_27691,c_11102,c_1956,c_1892,c_36,c_35,c_34]) ).
% 7.79/1.51  
% 7.79/1.51  
% 7.79/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.79/1.51  
% 7.79/1.51  ------                               Statistics
% 7.79/1.51  
% 7.79/1.51  ------ Selected
% 7.79/1.51  
% 7.79/1.51  total_time:                             0.731
% 7.79/1.51  
%------------------------------------------------------------------------------
