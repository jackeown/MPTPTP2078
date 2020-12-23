%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:54 EST 2020

% Result     : Theorem 8.01s
% Output     : CNFRefutation 8.01s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1689)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_pre_topc(X0)
             => ( ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                | k1_xboole_0 = X1 ) )
            & ( k1_xboole_0 = X1
             => ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v2_pre_topc(X0)
               => ( ( v2_compts_1(X1,X0)
                  <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                  | k1_xboole_0 = X1 ) )
              & ( k1_xboole_0 = X1
               => ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                | k1_xboole_0 = X1 )
              & ( k1_xboole_0 = X1
               => ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 != X1 )
            | ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 = X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ( ( v2_compts_1(X1,X0)
        <~> v1_compts_1(k1_pre_topc(X0,X1)) )
        & k1_xboole_0 = X1 )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 != X1 )
            | sP0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f24,f25])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
                | ~ v2_compts_1(X1,X0) )
              & ( v1_compts_1(k1_pre_topc(X0,X1))
                | v2_compts_1(X1,X0) )
              & k1_xboole_0 != X1 )
            | sP0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
                | ~ v2_compts_1(X1,X0) )
              & ( v1_compts_1(k1_pre_topc(X0,X1))
                | v2_compts_1(X1,X0) )
              & k1_xboole_0 != X1 )
            | sP0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
                | ~ v2_compts_1(X1,X0) )
              & ( v1_compts_1(k1_pre_topc(X0,X1))
                | v2_compts_1(X1,X0) )
              & k1_xboole_0 != X1 )
            | sP0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ( ( ~ v1_compts_1(k1_pre_topc(X0,sK3))
              | ~ v2_compts_1(sK3,X0) )
            & ( v1_compts_1(k1_pre_topc(X0,sK3))
              | v2_compts_1(sK3,X0) )
            & k1_xboole_0 != sK3 )
          | sP0(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
                  | ~ v2_compts_1(X1,X0) )
                & ( v1_compts_1(k1_pre_topc(X0,X1))
                  | v2_compts_1(X1,X0) )
                & k1_xboole_0 != X1 )
              | sP0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ( ( ~ v1_compts_1(k1_pre_topc(sK2,X1))
                | ~ v2_compts_1(X1,sK2) )
              & ( v1_compts_1(k1_pre_topc(sK2,X1))
                | v2_compts_1(X1,sK2) )
              & k1_xboole_0 != X1 )
            | sP0(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ( ( ~ v1_compts_1(k1_pre_topc(sK2,sK3))
          | ~ v2_compts_1(sK3,sK2) )
        & ( v1_compts_1(k1_pre_topc(sK2,sK3))
          | v2_compts_1(sK3,sK2) )
        & k1_xboole_0 != sK3 )
      | sP0(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f41,f40])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,k2_struct_0(X1))
               => ( v2_compts_1(X2,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => v2_compts_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v2_compts_1(X3,X1)
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK1(X1,X2),X1)
        & sK1(X1,X2) = X2
        & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ( ~ v2_compts_1(sK1(X1,X2),X1)
                    & sK1(X1,X2) = X2
                    & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | sK1(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ~ v2_compts_1(k2_struct_0(X0),X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_compts_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
          | ~ v2_compts_1(X1,X0) )
        & ( v1_compts_1(k1_pre_topc(X0,X1))
          | v2_compts_1(X1,X0) )
        & k1_xboole_0 = X1 )
      | ~ sP0(X1,X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
          | ~ v2_compts_1(X1,X0) )
        & ( v1_compts_1(k1_pre_topc(X0,X1))
          | v2_compts_1(X1,X0) )
        & k1_xboole_0 = X1 )
      | ~ sP0(X1,X0) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X1,X0))
          | ~ v2_compts_1(X0,X1) )
        & ( v1_compts_1(k1_pre_topc(X1,X0))
          | v2_compts_1(X0,X1) )
        & k1_xboole_0 = X0 )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f36])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(k1_pre_topc(X1,X0))
      | ~ v2_compts_1(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK2,sK3))
    | ~ v2_compts_1(sK3,sK2)
    | sP0(sK3,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_compts_1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( v2_compts_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X4,X0)
      | ~ r1_tarski(X4,k2_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0] :
      ( v2_compts_1(k2_struct_0(X0),X0)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X1,X0))
      | v2_compts_1(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,
    ( v1_compts_1(k1_pre_topc(sK2,sK3))
    | v2_compts_1(sK3,sK2)
    | sP0(sK3,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(sK1(X1,X2),X1)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1294,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_7,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_154,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_7])).

cnf(c_155,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_154])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_160,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_155,c_8])).

cnf(c_161,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_160])).

cnf(c_1292,plain,
    ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_161])).

cnf(c_1590,plain,
    ( k2_struct_0(k1_pre_topc(sK2,sK3)) = sK3
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1294,c_1292])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1793,plain,
    ( k2_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1590,c_26])).

cnf(c_15,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK1(X2,X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1297,plain,
    ( sK1(X0,X1) = X1
    | v2_compts_1(X1,X2) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | r1_tarski(X1,k2_struct_0(X0)) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2835,plain,
    ( sK1(X0,sK3) = sK3
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1294,c_1297])).

cnf(c_3077,plain,
    ( r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | sK1(X0,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2835,c_26])).

cnf(c_3078,plain,
    ( sK1(X0,sK3) = sK3
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3077])).

cnf(c_3083,plain,
    ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1793,c_3078])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1500,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1501,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1500])).

cnf(c_1477,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1611,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1477])).

cnf(c_1612,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1611])).

cnf(c_12,plain,
    ( ~ v2_compts_1(k2_struct_0(X0),X0)
    | v1_compts_1(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1)
    | ~ v2_compts_1(X0,X1)
    | ~ v1_compts_1(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,negated_conjecture,
    ( sP0(sK3,sK2)
    | ~ v2_compts_1(sK3,sK2)
    | ~ v1_compts_1(k1_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_388,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK3,sK2)
    | ~ v1_compts_1(k1_pre_topc(X1,X0))
    | ~ v1_compts_1(k1_pre_topc(sK2,sK3))
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_389,plain,
    ( ~ v2_compts_1(sK3,sK2)
    | ~ v1_compts_1(k1_pre_topc(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_408,plain,
    ( ~ v2_compts_1(k2_struct_0(X0),X0)
    | ~ v2_compts_1(sK3,sK2)
    | ~ l1_pre_topc(X0)
    | k1_pre_topc(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_389])).

cnf(c_409,plain,
    ( ~ v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3))
    | ~ v2_compts_1(sK3,sK2)
    | ~ l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_1291,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(c_1796,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1793,c_1291])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1367,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK2,sK3),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1368,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1367])).

cnf(c_1370,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_1892,plain,
    ( v2_compts_1(sK3,sK2) != iProver_top
    | v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1796,c_26,c_27,c_1370,c_1612])).

cnf(c_1893,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1892])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1305,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1308,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1305,c_3])).

cnf(c_17,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1295,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2181,plain,
    ( v2_compts_1(u1_struct_0(X0),X1) != iProver_top
    | v2_compts_1(u1_struct_0(X0),X0) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1308,c_1295])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1299,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2294,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1308,c_1299])).

cnf(c_7940,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_compts_1(u1_struct_0(X0),X0) = iProver_top
    | v2_compts_1(u1_struct_0(X0),X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2181,c_2294])).

cnf(c_7941,plain,
    ( v2_compts_1(u1_struct_0(X0),X1) != iProver_top
    | v2_compts_1(u1_struct_0(X0),X0) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7940])).

cnf(c_7950,plain,
    ( v2_compts_1(u1_struct_0(k1_pre_topc(sK2,sK3)),X0) != iProver_top
    | v2_compts_1(u1_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),X0) != iProver_top
    | r1_tarski(u1_struct_0(k1_pre_topc(sK2,sK3)),sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1793,c_7941])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1300,plain,
    ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1704,plain,
    ( u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1294,c_1300])).

cnf(c_1633,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k1_pre_topc(X0,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1635,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1633])).

cnf(c_1800,plain,
    ( u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1704,c_25,c_24,c_1635])).

cnf(c_7959,plain,
    ( v2_compts_1(sK3,X0) != iProver_top
    | v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),X0) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7950,c_1800])).

cnf(c_13,plain,
    ( v2_compts_1(k2_struct_0(X0),X0)
    | ~ v1_compts_1(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1)
    | v2_compts_1(X0,X1)
    | v1_compts_1(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_22,negated_conjecture,
    ( sP0(sK3,sK2)
    | v2_compts_1(sK3,sK2)
    | v1_compts_1(k1_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_361,plain,
    ( v2_compts_1(X0,X1)
    | v2_compts_1(sK3,sK2)
    | v1_compts_1(k1_pre_topc(X1,X0))
    | v1_compts_1(k1_pre_topc(sK2,sK3))
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_362,plain,
    ( v2_compts_1(sK3,sK2)
    | v1_compts_1(k1_pre_topc(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_421,plain,
    ( v2_compts_1(k2_struct_0(X0),X0)
    | v2_compts_1(sK3,sK2)
    | ~ l1_pre_topc(X0)
    | k1_pre_topc(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_362])).

cnf(c_422,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3))
    | v2_compts_1(sK3,sK2)
    | ~ l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_1290,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_1795,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1793,c_1290])).

cnf(c_2000,plain,
    ( v2_compts_1(sK3,sK2) = iProver_top
    | v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1795,c_26,c_27,c_1370,c_1612])).

cnf(c_2001,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_2000])).

cnf(c_7979,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7959])).

cnf(c_8868,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7959,c_26,c_27,c_1501,c_1612,c_2001,c_7979])).

cnf(c_18512,plain,
    ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3083,c_26,c_27,c_1501,c_1590,c_1612,c_1689,c_1772,c_1893,c_2001,c_7979])).

cnf(c_14,plain,
    ( v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK1(X2,X0),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1298,plain,
    ( v2_compts_1(X0,X1) = iProver_top
    | v2_compts_1(sK1(X2,X0),X2) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2854,plain,
    ( v2_compts_1(sK1(X0,sK3),X0) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1294,c_1298])).

cnf(c_2955,plain,
    ( r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | v2_compts_1(sK1(X0,sK3),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2854,c_26])).

cnf(c_2956,plain,
    ( v2_compts_1(sK1(X0,sK3),X0) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2955])).

cnf(c_18523,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18512,c_2956])).

cnf(c_18525,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18523,c_1793])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18525,c_8868,c_1893,c_1612,c_1501,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:17:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 8.01/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.01/1.49  
% 8.01/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.01/1.49  
% 8.01/1.49  ------  iProver source info
% 8.01/1.49  
% 8.01/1.49  git: date: 2020-06-30 10:37:57 +0100
% 8.01/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.01/1.49  git: non_committed_changes: false
% 8.01/1.49  git: last_make_outside_of_git: false
% 8.01/1.49  
% 8.01/1.49  ------ 
% 8.01/1.49  
% 8.01/1.49  ------ Input Options
% 8.01/1.49  
% 8.01/1.49  --out_options                           all
% 8.01/1.49  --tptp_safe_out                         true
% 8.01/1.49  --problem_path                          ""
% 8.01/1.49  --include_path                          ""
% 8.01/1.49  --clausifier                            res/vclausify_rel
% 8.01/1.49  --clausifier_options                    ""
% 8.01/1.49  --stdin                                 false
% 8.01/1.49  --stats_out                             all
% 8.01/1.49  
% 8.01/1.49  ------ General Options
% 8.01/1.49  
% 8.01/1.49  --fof                                   false
% 8.01/1.49  --time_out_real                         305.
% 8.01/1.49  --time_out_virtual                      -1.
% 8.01/1.49  --symbol_type_check                     false
% 8.01/1.49  --clausify_out                          false
% 8.01/1.49  --sig_cnt_out                           false
% 8.01/1.49  --trig_cnt_out                          false
% 8.01/1.49  --trig_cnt_out_tolerance                1.
% 8.01/1.49  --trig_cnt_out_sk_spl                   false
% 8.01/1.49  --abstr_cl_out                          false
% 8.01/1.49  
% 8.01/1.49  ------ Global Options
% 8.01/1.49  
% 8.01/1.49  --schedule                              default
% 8.01/1.49  --add_important_lit                     false
% 8.01/1.49  --prop_solver_per_cl                    1000
% 8.01/1.49  --min_unsat_core                        false
% 8.01/1.49  --soft_assumptions                      false
% 8.01/1.49  --soft_lemma_size                       3
% 8.01/1.49  --prop_impl_unit_size                   0
% 8.01/1.49  --prop_impl_unit                        []
% 8.01/1.49  --share_sel_clauses                     true
% 8.01/1.49  --reset_solvers                         false
% 8.01/1.49  --bc_imp_inh                            [conj_cone]
% 8.01/1.49  --conj_cone_tolerance                   3.
% 8.01/1.49  --extra_neg_conj                        none
% 8.01/1.49  --large_theory_mode                     true
% 8.01/1.49  --prolific_symb_bound                   200
% 8.01/1.49  --lt_threshold                          2000
% 8.01/1.49  --clause_weak_htbl                      true
% 8.01/1.49  --gc_record_bc_elim                     false
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing Options
% 8.01/1.49  
% 8.01/1.49  --preprocessing_flag                    true
% 8.01/1.49  --time_out_prep_mult                    0.1
% 8.01/1.49  --splitting_mode                        input
% 8.01/1.49  --splitting_grd                         true
% 8.01/1.49  --splitting_cvd                         false
% 8.01/1.49  --splitting_cvd_svl                     false
% 8.01/1.49  --splitting_nvd                         32
% 8.01/1.49  --sub_typing                            true
% 8.01/1.49  --prep_gs_sim                           true
% 8.01/1.49  --prep_unflatten                        true
% 8.01/1.49  --prep_res_sim                          true
% 8.01/1.49  --prep_upred                            true
% 8.01/1.49  --prep_sem_filter                       exhaustive
% 8.01/1.49  --prep_sem_filter_out                   false
% 8.01/1.49  --pred_elim                             true
% 8.01/1.49  --res_sim_input                         true
% 8.01/1.49  --eq_ax_congr_red                       true
% 8.01/1.49  --pure_diseq_elim                       true
% 8.01/1.49  --brand_transform                       false
% 8.01/1.49  --non_eq_to_eq                          false
% 8.01/1.49  --prep_def_merge                        true
% 8.01/1.49  --prep_def_merge_prop_impl              false
% 8.01/1.49  --prep_def_merge_mbd                    true
% 8.01/1.49  --prep_def_merge_tr_red                 false
% 8.01/1.49  --prep_def_merge_tr_cl                  false
% 8.01/1.49  --smt_preprocessing                     true
% 8.01/1.49  --smt_ac_axioms                         fast
% 8.01/1.49  --preprocessed_out                      false
% 8.01/1.49  --preprocessed_stats                    false
% 8.01/1.49  
% 8.01/1.49  ------ Abstraction refinement Options
% 8.01/1.49  
% 8.01/1.49  --abstr_ref                             []
% 8.01/1.49  --abstr_ref_prep                        false
% 8.01/1.49  --abstr_ref_until_sat                   false
% 8.01/1.49  --abstr_ref_sig_restrict                funpre
% 8.01/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.01/1.49  --abstr_ref_under                       []
% 8.01/1.49  
% 8.01/1.49  ------ SAT Options
% 8.01/1.49  
% 8.01/1.49  --sat_mode                              false
% 8.01/1.49  --sat_fm_restart_options                ""
% 8.01/1.49  --sat_gr_def                            false
% 8.01/1.49  --sat_epr_types                         true
% 8.01/1.49  --sat_non_cyclic_types                  false
% 8.01/1.49  --sat_finite_models                     false
% 8.01/1.49  --sat_fm_lemmas                         false
% 8.01/1.49  --sat_fm_prep                           false
% 8.01/1.49  --sat_fm_uc_incr                        true
% 8.01/1.49  --sat_out_model                         small
% 8.01/1.49  --sat_out_clauses                       false
% 8.01/1.49  
% 8.01/1.49  ------ QBF Options
% 8.01/1.49  
% 8.01/1.49  --qbf_mode                              false
% 8.01/1.49  --qbf_elim_univ                         false
% 8.01/1.49  --qbf_dom_inst                          none
% 8.01/1.49  --qbf_dom_pre_inst                      false
% 8.01/1.49  --qbf_sk_in                             false
% 8.01/1.49  --qbf_pred_elim                         true
% 8.01/1.49  --qbf_split                             512
% 8.01/1.49  
% 8.01/1.49  ------ BMC1 Options
% 8.01/1.49  
% 8.01/1.49  --bmc1_incremental                      false
% 8.01/1.49  --bmc1_axioms                           reachable_all
% 8.01/1.49  --bmc1_min_bound                        0
% 8.01/1.49  --bmc1_max_bound                        -1
% 8.01/1.49  --bmc1_max_bound_default                -1
% 8.01/1.49  --bmc1_symbol_reachability              true
% 8.01/1.49  --bmc1_property_lemmas                  false
% 8.01/1.49  --bmc1_k_induction                      false
% 8.01/1.49  --bmc1_non_equiv_states                 false
% 8.01/1.49  --bmc1_deadlock                         false
% 8.01/1.49  --bmc1_ucm                              false
% 8.01/1.49  --bmc1_add_unsat_core                   none
% 8.01/1.49  --bmc1_unsat_core_children              false
% 8.01/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.01/1.49  --bmc1_out_stat                         full
% 8.01/1.49  --bmc1_ground_init                      false
% 8.01/1.49  --bmc1_pre_inst_next_state              false
% 8.01/1.49  --bmc1_pre_inst_state                   false
% 8.01/1.49  --bmc1_pre_inst_reach_state             false
% 8.01/1.49  --bmc1_out_unsat_core                   false
% 8.01/1.49  --bmc1_aig_witness_out                  false
% 8.01/1.49  --bmc1_verbose                          false
% 8.01/1.49  --bmc1_dump_clauses_tptp                false
% 8.01/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.01/1.49  --bmc1_dump_file                        -
% 8.01/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.01/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.01/1.49  --bmc1_ucm_extend_mode                  1
% 8.01/1.49  --bmc1_ucm_init_mode                    2
% 8.01/1.49  --bmc1_ucm_cone_mode                    none
% 8.01/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.01/1.49  --bmc1_ucm_relax_model                  4
% 8.01/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.01/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.01/1.49  --bmc1_ucm_layered_model                none
% 8.01/1.49  --bmc1_ucm_max_lemma_size               10
% 8.01/1.49  
% 8.01/1.49  ------ AIG Options
% 8.01/1.49  
% 8.01/1.49  --aig_mode                              false
% 8.01/1.49  
% 8.01/1.49  ------ Instantiation Options
% 8.01/1.49  
% 8.01/1.49  --instantiation_flag                    true
% 8.01/1.49  --inst_sos_flag                         true
% 8.01/1.49  --inst_sos_phase                        true
% 8.01/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.01/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.01/1.49  --inst_lit_sel_side                     num_symb
% 8.01/1.49  --inst_solver_per_active                1400
% 8.01/1.49  --inst_solver_calls_frac                1.
% 8.01/1.49  --inst_passive_queue_type               priority_queues
% 8.01/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.01/1.49  --inst_passive_queues_freq              [25;2]
% 8.01/1.49  --inst_dismatching                      true
% 8.01/1.49  --inst_eager_unprocessed_to_passive     true
% 8.01/1.49  --inst_prop_sim_given                   true
% 8.01/1.49  --inst_prop_sim_new                     false
% 8.01/1.49  --inst_subs_new                         false
% 8.01/1.49  --inst_eq_res_simp                      false
% 8.01/1.49  --inst_subs_given                       false
% 8.01/1.49  --inst_orphan_elimination               true
% 8.01/1.49  --inst_learning_loop_flag               true
% 8.01/1.49  --inst_learning_start                   3000
% 8.01/1.49  --inst_learning_factor                  2
% 8.01/1.49  --inst_start_prop_sim_after_learn       3
% 8.01/1.49  --inst_sel_renew                        solver
% 8.01/1.49  --inst_lit_activity_flag                true
% 8.01/1.49  --inst_restr_to_given                   false
% 8.01/1.49  --inst_activity_threshold               500
% 8.01/1.49  --inst_out_proof                        true
% 8.01/1.49  
% 8.01/1.49  ------ Resolution Options
% 8.01/1.49  
% 8.01/1.49  --resolution_flag                       true
% 8.01/1.49  --res_lit_sel                           adaptive
% 8.01/1.49  --res_lit_sel_side                      none
% 8.01/1.49  --res_ordering                          kbo
% 8.01/1.49  --res_to_prop_solver                    active
% 8.01/1.49  --res_prop_simpl_new                    false
% 8.01/1.49  --res_prop_simpl_given                  true
% 8.01/1.49  --res_passive_queue_type                priority_queues
% 8.01/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.01/1.49  --res_passive_queues_freq               [15;5]
% 8.01/1.49  --res_forward_subs                      full
% 8.01/1.49  --res_backward_subs                     full
% 8.01/1.49  --res_forward_subs_resolution           true
% 8.01/1.49  --res_backward_subs_resolution          true
% 8.01/1.49  --res_orphan_elimination                true
% 8.01/1.49  --res_time_limit                        2.
% 8.01/1.49  --res_out_proof                         true
% 8.01/1.49  
% 8.01/1.49  ------ Superposition Options
% 8.01/1.49  
% 8.01/1.49  --superposition_flag                    true
% 8.01/1.49  --sup_passive_queue_type                priority_queues
% 8.01/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.01/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.01/1.49  --demod_completeness_check              fast
% 8.01/1.49  --demod_use_ground                      true
% 8.01/1.49  --sup_to_prop_solver                    passive
% 8.01/1.49  --sup_prop_simpl_new                    true
% 8.01/1.49  --sup_prop_simpl_given                  true
% 8.01/1.49  --sup_fun_splitting                     true
% 8.01/1.49  --sup_smt_interval                      50000
% 8.01/1.49  
% 8.01/1.49  ------ Superposition Simplification Setup
% 8.01/1.49  
% 8.01/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.01/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.01/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.01/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.01/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.01/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.01/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.01/1.49  --sup_immed_triv                        [TrivRules]
% 8.01/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.49  --sup_immed_bw_main                     []
% 8.01/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.01/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.01/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.49  --sup_input_bw                          []
% 8.01/1.49  
% 8.01/1.49  ------ Combination Options
% 8.01/1.49  
% 8.01/1.49  --comb_res_mult                         3
% 8.01/1.49  --comb_sup_mult                         2
% 8.01/1.49  --comb_inst_mult                        10
% 8.01/1.49  
% 8.01/1.49  ------ Debug Options
% 8.01/1.49  
% 8.01/1.49  --dbg_backtrace                         false
% 8.01/1.49  --dbg_dump_prop_clauses                 false
% 8.01/1.49  --dbg_dump_prop_clauses_file            -
% 8.01/1.49  --dbg_out_stat                          false
% 8.01/1.49  ------ Parsing...
% 8.01/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.01/1.49  ------ Proving...
% 8.01/1.49  ------ Problem Properties 
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  clauses                                 20
% 8.01/1.49  conjectures                             2
% 8.01/1.49  EPR                                     5
% 8.01/1.49  Horn                                    17
% 8.01/1.49  unary                                   5
% 8.01/1.49  binary                                  1
% 8.01/1.49  lits                                    65
% 8.01/1.49  lits eq                                 8
% 8.01/1.49  fd_pure                                 0
% 8.01/1.49  fd_pseudo                               0
% 8.01/1.49  fd_cond                                 0
% 8.01/1.49  fd_pseudo_cond                          1
% 8.01/1.49  AC symbols                              0
% 8.01/1.49  
% 8.01/1.49  ------ Schedule dynamic 5 is on 
% 8.01/1.49  
% 8.01/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  ------ 
% 8.01/1.49  Current options:
% 8.01/1.49  ------ 
% 8.01/1.49  
% 8.01/1.49  ------ Input Options
% 8.01/1.49  
% 8.01/1.49  --out_options                           all
% 8.01/1.49  --tptp_safe_out                         true
% 8.01/1.49  --problem_path                          ""
% 8.01/1.49  --include_path                          ""
% 8.01/1.49  --clausifier                            res/vclausify_rel
% 8.01/1.49  --clausifier_options                    ""
% 8.01/1.49  --stdin                                 false
% 8.01/1.49  --stats_out                             all
% 8.01/1.49  
% 8.01/1.49  ------ General Options
% 8.01/1.49  
% 8.01/1.49  --fof                                   false
% 8.01/1.49  --time_out_real                         305.
% 8.01/1.49  --time_out_virtual                      -1.
% 8.01/1.49  --symbol_type_check                     false
% 8.01/1.49  --clausify_out                          false
% 8.01/1.49  --sig_cnt_out                           false
% 8.01/1.49  --trig_cnt_out                          false
% 8.01/1.49  --trig_cnt_out_tolerance                1.
% 8.01/1.49  --trig_cnt_out_sk_spl                   false
% 8.01/1.49  --abstr_cl_out                          false
% 8.01/1.49  
% 8.01/1.49  ------ Global Options
% 8.01/1.49  
% 8.01/1.49  --schedule                              default
% 8.01/1.49  --add_important_lit                     false
% 8.01/1.49  --prop_solver_per_cl                    1000
% 8.01/1.49  --min_unsat_core                        false
% 8.01/1.49  --soft_assumptions                      false
% 8.01/1.49  --soft_lemma_size                       3
% 8.01/1.49  --prop_impl_unit_size                   0
% 8.01/1.49  --prop_impl_unit                        []
% 8.01/1.49  --share_sel_clauses                     true
% 8.01/1.49  --reset_solvers                         false
% 8.01/1.49  --bc_imp_inh                            [conj_cone]
% 8.01/1.49  --conj_cone_tolerance                   3.
% 8.01/1.49  --extra_neg_conj                        none
% 8.01/1.49  --large_theory_mode                     true
% 8.01/1.49  --prolific_symb_bound                   200
% 8.01/1.49  --lt_threshold                          2000
% 8.01/1.49  --clause_weak_htbl                      true
% 8.01/1.49  --gc_record_bc_elim                     false
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing Options
% 8.01/1.49  
% 8.01/1.49  --preprocessing_flag                    true
% 8.01/1.49  --time_out_prep_mult                    0.1
% 8.01/1.49  --splitting_mode                        input
% 8.01/1.49  --splitting_grd                         true
% 8.01/1.49  --splitting_cvd                         false
% 8.01/1.49  --splitting_cvd_svl                     false
% 8.01/1.49  --splitting_nvd                         32
% 8.01/1.49  --sub_typing                            true
% 8.01/1.49  --prep_gs_sim                           true
% 8.01/1.49  --prep_unflatten                        true
% 8.01/1.49  --prep_res_sim                          true
% 8.01/1.49  --prep_upred                            true
% 8.01/1.49  --prep_sem_filter                       exhaustive
% 8.01/1.49  --prep_sem_filter_out                   false
% 8.01/1.49  --pred_elim                             true
% 8.01/1.49  --res_sim_input                         true
% 8.01/1.49  --eq_ax_congr_red                       true
% 8.01/1.49  --pure_diseq_elim                       true
% 8.01/1.49  --brand_transform                       false
% 8.01/1.49  --non_eq_to_eq                          false
% 8.01/1.49  --prep_def_merge                        true
% 8.01/1.49  --prep_def_merge_prop_impl              false
% 8.01/1.49  --prep_def_merge_mbd                    true
% 8.01/1.49  --prep_def_merge_tr_red                 false
% 8.01/1.49  --prep_def_merge_tr_cl                  false
% 8.01/1.49  --smt_preprocessing                     true
% 8.01/1.49  --smt_ac_axioms                         fast
% 8.01/1.49  --preprocessed_out                      false
% 8.01/1.49  --preprocessed_stats                    false
% 8.01/1.49  
% 8.01/1.49  ------ Abstraction refinement Options
% 8.01/1.49  
% 8.01/1.49  --abstr_ref                             []
% 8.01/1.49  --abstr_ref_prep                        false
% 8.01/1.49  --abstr_ref_until_sat                   false
% 8.01/1.49  --abstr_ref_sig_restrict                funpre
% 8.01/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.01/1.49  --abstr_ref_under                       []
% 8.01/1.49  
% 8.01/1.49  ------ SAT Options
% 8.01/1.49  
% 8.01/1.49  --sat_mode                              false
% 8.01/1.49  --sat_fm_restart_options                ""
% 8.01/1.49  --sat_gr_def                            false
% 8.01/1.49  --sat_epr_types                         true
% 8.01/1.49  --sat_non_cyclic_types                  false
% 8.01/1.49  --sat_finite_models                     false
% 8.01/1.49  --sat_fm_lemmas                         false
% 8.01/1.49  --sat_fm_prep                           false
% 8.01/1.49  --sat_fm_uc_incr                        true
% 8.01/1.49  --sat_out_model                         small
% 8.01/1.49  --sat_out_clauses                       false
% 8.01/1.49  
% 8.01/1.49  ------ QBF Options
% 8.01/1.49  
% 8.01/1.49  --qbf_mode                              false
% 8.01/1.49  --qbf_elim_univ                         false
% 8.01/1.49  --qbf_dom_inst                          none
% 8.01/1.49  --qbf_dom_pre_inst                      false
% 8.01/1.49  --qbf_sk_in                             false
% 8.01/1.49  --qbf_pred_elim                         true
% 8.01/1.49  --qbf_split                             512
% 8.01/1.49  
% 8.01/1.49  ------ BMC1 Options
% 8.01/1.49  
% 8.01/1.49  --bmc1_incremental                      false
% 8.01/1.49  --bmc1_axioms                           reachable_all
% 8.01/1.49  --bmc1_min_bound                        0
% 8.01/1.49  --bmc1_max_bound                        -1
% 8.01/1.49  --bmc1_max_bound_default                -1
% 8.01/1.49  --bmc1_symbol_reachability              true
% 8.01/1.49  --bmc1_property_lemmas                  false
% 8.01/1.49  --bmc1_k_induction                      false
% 8.01/1.49  --bmc1_non_equiv_states                 false
% 8.01/1.49  --bmc1_deadlock                         false
% 8.01/1.49  --bmc1_ucm                              false
% 8.01/1.49  --bmc1_add_unsat_core                   none
% 8.01/1.49  --bmc1_unsat_core_children              false
% 8.01/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.01/1.49  --bmc1_out_stat                         full
% 8.01/1.49  --bmc1_ground_init                      false
% 8.01/1.49  --bmc1_pre_inst_next_state              false
% 8.01/1.49  --bmc1_pre_inst_state                   false
% 8.01/1.49  --bmc1_pre_inst_reach_state             false
% 8.01/1.49  --bmc1_out_unsat_core                   false
% 8.01/1.49  --bmc1_aig_witness_out                  false
% 8.01/1.49  --bmc1_verbose                          false
% 8.01/1.49  --bmc1_dump_clauses_tptp                false
% 8.01/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.01/1.49  --bmc1_dump_file                        -
% 8.01/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.01/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.01/1.49  --bmc1_ucm_extend_mode                  1
% 8.01/1.49  --bmc1_ucm_init_mode                    2
% 8.01/1.49  --bmc1_ucm_cone_mode                    none
% 8.01/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.01/1.49  --bmc1_ucm_relax_model                  4
% 8.01/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.01/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.01/1.49  --bmc1_ucm_layered_model                none
% 8.01/1.49  --bmc1_ucm_max_lemma_size               10
% 8.01/1.49  
% 8.01/1.49  ------ AIG Options
% 8.01/1.49  
% 8.01/1.49  --aig_mode                              false
% 8.01/1.49  
% 8.01/1.49  ------ Instantiation Options
% 8.01/1.49  
% 8.01/1.49  --instantiation_flag                    true
% 8.01/1.49  --inst_sos_flag                         true
% 8.01/1.49  --inst_sos_phase                        true
% 8.01/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.01/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.01/1.49  --inst_lit_sel_side                     none
% 8.01/1.49  --inst_solver_per_active                1400
% 8.01/1.49  --inst_solver_calls_frac                1.
% 8.01/1.49  --inst_passive_queue_type               priority_queues
% 8.01/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.01/1.49  --inst_passive_queues_freq              [25;2]
% 8.01/1.49  --inst_dismatching                      true
% 8.01/1.49  --inst_eager_unprocessed_to_passive     true
% 8.01/1.49  --inst_prop_sim_given                   true
% 8.01/1.49  --inst_prop_sim_new                     false
% 8.01/1.49  --inst_subs_new                         false
% 8.01/1.49  --inst_eq_res_simp                      false
% 8.01/1.49  --inst_subs_given                       false
% 8.01/1.49  --inst_orphan_elimination               true
% 8.01/1.49  --inst_learning_loop_flag               true
% 8.01/1.49  --inst_learning_start                   3000
% 8.01/1.49  --inst_learning_factor                  2
% 8.01/1.49  --inst_start_prop_sim_after_learn       3
% 8.01/1.49  --inst_sel_renew                        solver
% 8.01/1.49  --inst_lit_activity_flag                true
% 8.01/1.49  --inst_restr_to_given                   false
% 8.01/1.49  --inst_activity_threshold               500
% 8.01/1.49  --inst_out_proof                        true
% 8.01/1.49  
% 8.01/1.49  ------ Resolution Options
% 8.01/1.49  
% 8.01/1.49  --resolution_flag                       false
% 8.01/1.49  --res_lit_sel                           adaptive
% 8.01/1.49  --res_lit_sel_side                      none
% 8.01/1.49  --res_ordering                          kbo
% 8.01/1.49  --res_to_prop_solver                    active
% 8.01/1.49  --res_prop_simpl_new                    false
% 8.01/1.49  --res_prop_simpl_given                  true
% 8.01/1.49  --res_passive_queue_type                priority_queues
% 8.01/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.01/1.49  --res_passive_queues_freq               [15;5]
% 8.01/1.49  --res_forward_subs                      full
% 8.01/1.49  --res_backward_subs                     full
% 8.01/1.49  --res_forward_subs_resolution           true
% 8.01/1.49  --res_backward_subs_resolution          true
% 8.01/1.49  --res_orphan_elimination                true
% 8.01/1.49  --res_time_limit                        2.
% 8.01/1.49  --res_out_proof                         true
% 8.01/1.49  
% 8.01/1.49  ------ Superposition Options
% 8.01/1.49  
% 8.01/1.49  --superposition_flag                    true
% 8.01/1.49  --sup_passive_queue_type                priority_queues
% 8.01/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.01/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.01/1.49  --demod_completeness_check              fast
% 8.01/1.49  --demod_use_ground                      true
% 8.01/1.49  --sup_to_prop_solver                    passive
% 8.01/1.49  --sup_prop_simpl_new                    true
% 8.01/1.49  --sup_prop_simpl_given                  true
% 8.01/1.49  --sup_fun_splitting                     true
% 8.01/1.49  --sup_smt_interval                      50000
% 8.01/1.49  
% 8.01/1.49  ------ Superposition Simplification Setup
% 8.01/1.49  
% 8.01/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.01/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.01/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.01/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.01/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.01/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.01/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.01/1.49  --sup_immed_triv                        [TrivRules]
% 8.01/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.49  --sup_immed_bw_main                     []
% 8.01/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.01/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.01/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.49  --sup_input_bw                          []
% 8.01/1.49  
% 8.01/1.49  ------ Combination Options
% 8.01/1.49  
% 8.01/1.49  --comb_res_mult                         3
% 8.01/1.49  --comb_sup_mult                         2
% 8.01/1.49  --comb_inst_mult                        10
% 8.01/1.49  
% 8.01/1.49  ------ Debug Options
% 8.01/1.49  
% 8.01/1.49  --dbg_backtrace                         false
% 8.01/1.49  --dbg_dump_prop_clauses                 false
% 8.01/1.49  --dbg_dump_prop_clauses_file            -
% 8.01/1.49  --dbg_out_stat                          false
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  ------ Proving...
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  % SZS status Theorem for theBenchmark.p
% 8.01/1.49  
% 8.01/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.01/1.49  
% 8.01/1.49  fof(f11,conjecture,(
% 8.01/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 8.01/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f12,negated_conjecture,(
% 8.01/1.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 8.01/1.49    inference(negated_conjecture,[],[f11])).
% 8.01/1.49  
% 8.01/1.49  fof(f13,plain,(
% 8.01/1.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 8.01/1.49    inference(pure_predicate_removal,[],[f12])).
% 8.01/1.49  
% 8.01/1.49  fof(f24,plain,(
% 8.01/1.49    ? [X0] : (? [X1] : ((((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 != X1) | ((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f13])).
% 8.01/1.49  
% 8.01/1.49  fof(f25,plain,(
% 8.01/1.49    ! [X1,X0] : (((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 = X1) | ~sP0(X1,X0))),
% 8.01/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 8.01/1.49  
% 8.01/1.49  fof(f26,plain,(
% 8.01/1.49    ? [X0] : (? [X1] : ((((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 8.01/1.49    inference(definition_folding,[],[f24,f25])).
% 8.01/1.49  
% 8.01/1.49  fof(f38,plain,(
% 8.01/1.49    ? [X0] : (? [X1] : (((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0))) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 8.01/1.49    inference(nnf_transformation,[],[f26])).
% 8.01/1.49  
% 8.01/1.49  fof(f39,plain,(
% 8.01/1.49    ? [X0] : (? [X1] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 8.01/1.49    inference(flattening,[],[f38])).
% 8.01/1.49  
% 8.01/1.49  fof(f41,plain,(
% 8.01/1.49    ( ! [X0] : (? [X1] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((((~v1_compts_1(k1_pre_topc(X0,sK3)) | ~v2_compts_1(sK3,X0)) & (v1_compts_1(k1_pre_topc(X0,sK3)) | v2_compts_1(sK3,X0)) & k1_xboole_0 != sK3) | sP0(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 8.01/1.49    introduced(choice_axiom,[])).
% 8.01/1.49  
% 8.01/1.49  fof(f40,plain,(
% 8.01/1.49    ? [X0] : (? [X1] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((((~v1_compts_1(k1_pre_topc(sK2,X1)) | ~v2_compts_1(X1,sK2)) & (v1_compts_1(k1_pre_topc(sK2,X1)) | v2_compts_1(X1,sK2)) & k1_xboole_0 != X1) | sP0(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 8.01/1.49    introduced(choice_axiom,[])).
% 8.01/1.49  
% 8.01/1.49  fof(f42,plain,(
% 8.01/1.49    ((((~v1_compts_1(k1_pre_topc(sK2,sK3)) | ~v2_compts_1(sK3,sK2)) & (v1_compts_1(k1_pre_topc(sK2,sK3)) | v2_compts_1(sK3,sK2)) & k1_xboole_0 != sK3) | sP0(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 8.01/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f41,f40])).
% 8.01/1.49  
% 8.01/1.49  fof(f65,plain,(
% 8.01/1.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 8.01/1.49    inference(cnf_transformation,[],[f42])).
% 8.01/1.49  
% 8.01/1.49  fof(f4,axiom,(
% 8.01/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 8.01/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f14,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f4])).
% 8.01/1.49  
% 8.01/1.49  fof(f15,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(flattening,[],[f14])).
% 8.01/1.49  
% 8.01/1.49  fof(f29,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(nnf_transformation,[],[f15])).
% 8.01/1.49  
% 8.01/1.49  fof(f48,plain,(
% 8.01/1.49    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f29])).
% 8.01/1.49  
% 8.01/1.49  fof(f72,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(equality_resolution,[],[f48])).
% 8.01/1.49  
% 8.01/1.49  fof(f5,axiom,(
% 8.01/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 8.01/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f16,plain,(
% 8.01/1.49    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 8.01/1.49    inference(ennf_transformation,[],[f5])).
% 8.01/1.49  
% 8.01/1.49  fof(f17,plain,(
% 8.01/1.49    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(flattening,[],[f16])).
% 8.01/1.49  
% 8.01/1.49  fof(f51,plain,(
% 8.01/1.49    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f17])).
% 8.01/1.49  
% 8.01/1.49  fof(f50,plain,(
% 8.01/1.49    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f17])).
% 8.01/1.49  
% 8.01/1.49  fof(f64,plain,(
% 8.01/1.49    l1_pre_topc(sK2)),
% 8.01/1.49    inference(cnf_transformation,[],[f42])).
% 8.01/1.49  
% 8.01/1.49  fof(f10,axiom,(
% 8.01/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 8.01/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f22,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f10])).
% 8.01/1.49  
% 8.01/1.49  fof(f23,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(flattening,[],[f22])).
% 8.01/1.49  
% 8.01/1.49  fof(f31,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(nnf_transformation,[],[f23])).
% 8.01/1.49  
% 8.01/1.49  fof(f32,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(rectify,[],[f31])).
% 8.01/1.49  
% 8.01/1.49  fof(f33,plain,(
% 8.01/1.49    ! [X2,X1] : (? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v2_compts_1(sK1(X1,X2),X1) & sK1(X1,X2) = X2 & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 8.01/1.49    introduced(choice_axiom,[])).
% 8.01/1.49  
% 8.01/1.49  fof(f34,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | (~v2_compts_1(sK1(X1,X2),X1) & sK1(X1,X2) = X2 & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 8.01/1.49  
% 8.01/1.49  fof(f59,plain,(
% 8.01/1.49    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | sK1(X1,X2) = X2 | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f34])).
% 8.01/1.49  
% 8.01/1.49  fof(f1,axiom,(
% 8.01/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.01/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f27,plain,(
% 8.01/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.01/1.49    inference(nnf_transformation,[],[f1])).
% 8.01/1.49  
% 8.01/1.49  fof(f28,plain,(
% 8.01/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.01/1.49    inference(flattening,[],[f27])).
% 8.01/1.49  
% 8.01/1.49  fof(f43,plain,(
% 8.01/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 8.01/1.49    inference(cnf_transformation,[],[f28])).
% 8.01/1.49  
% 8.01/1.49  fof(f70,plain,(
% 8.01/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 8.01/1.49    inference(equality_resolution,[],[f43])).
% 8.01/1.49  
% 8.01/1.49  fof(f9,axiom,(
% 8.01/1.49    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 8.01/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f21,plain,(
% 8.01/1.49    ! [X0] : ((v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f9])).
% 8.01/1.49  
% 8.01/1.49  fof(f30,plain,(
% 8.01/1.49    ! [X0] : (((v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0)) & (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(nnf_transformation,[],[f21])).
% 8.01/1.49  
% 8.01/1.49  fof(f56,plain,(
% 8.01/1.49    ( ! [X0] : (v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f30])).
% 8.01/1.49  
% 8.01/1.49  fof(f35,plain,(
% 8.01/1.49    ! [X1,X0] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0))) & k1_xboole_0 = X1) | ~sP0(X1,X0))),
% 8.01/1.49    inference(nnf_transformation,[],[f25])).
% 8.01/1.49  
% 8.01/1.49  fof(f36,plain,(
% 8.01/1.49    ! [X1,X0] : (((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 = X1) | ~sP0(X1,X0))),
% 8.01/1.49    inference(flattening,[],[f35])).
% 8.01/1.49  
% 8.01/1.49  fof(f37,plain,(
% 8.01/1.49    ! [X0,X1] : (((~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1)) & (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1)) & k1_xboole_0 = X0) | ~sP0(X0,X1))),
% 8.01/1.49    inference(rectify,[],[f36])).
% 8.01/1.49  
% 8.01/1.49  fof(f63,plain,(
% 8.01/1.49    ( ! [X0,X1] : (~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1) | ~sP0(X0,X1)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f37])).
% 8.01/1.49  
% 8.01/1.49  fof(f68,plain,(
% 8.01/1.49    ~v1_compts_1(k1_pre_topc(sK2,sK3)) | ~v2_compts_1(sK3,sK2) | sP0(sK3,sK2)),
% 8.01/1.49    inference(cnf_transformation,[],[f42])).
% 8.01/1.49  
% 8.01/1.49  fof(f6,axiom,(
% 8.01/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 8.01/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f18,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f6])).
% 8.01/1.49  
% 8.01/1.49  fof(f52,plain,(
% 8.01/1.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f18])).
% 8.01/1.49  
% 8.01/1.49  fof(f3,axiom,(
% 8.01/1.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 8.01/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f47,plain,(
% 8.01/1.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 8.01/1.49    inference(cnf_transformation,[],[f3])).
% 8.01/1.49  
% 8.01/1.49  fof(f2,axiom,(
% 8.01/1.49    ! [X0] : k2_subset_1(X0) = X0),
% 8.01/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f46,plain,(
% 8.01/1.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 8.01/1.49    inference(cnf_transformation,[],[f2])).
% 8.01/1.49  
% 8.01/1.49  fof(f57,plain,(
% 8.01/1.49    ( ! [X4,X2,X0,X1] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f34])).
% 8.01/1.49  
% 8.01/1.49  fof(f73,plain,(
% 8.01/1.49    ( ! [X4,X0,X1] : (v2_compts_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X4,X0) | ~r1_tarski(X4,k2_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(equality_resolution,[],[f57])).
% 8.01/1.49  
% 8.01/1.49  fof(f8,axiom,(
% 8.01/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 8.01/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f20,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f8])).
% 8.01/1.49  
% 8.01/1.49  fof(f54,plain,(
% 8.01/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f20])).
% 8.01/1.49  
% 8.01/1.49  fof(f7,axiom,(
% 8.01/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 8.01/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f19,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f7])).
% 8.01/1.49  
% 8.01/1.49  fof(f53,plain,(
% 8.01/1.49    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f19])).
% 8.01/1.49  
% 8.01/1.49  fof(f55,plain,(
% 8.01/1.49    ( ! [X0] : (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f30])).
% 8.01/1.49  
% 8.01/1.49  fof(f62,plain,(
% 8.01/1.49    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1) | ~sP0(X0,X1)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f37])).
% 8.01/1.49  
% 8.01/1.49  fof(f67,plain,(
% 8.01/1.49    v1_compts_1(k1_pre_topc(sK2,sK3)) | v2_compts_1(sK3,sK2) | sP0(sK3,sK2)),
% 8.01/1.49    inference(cnf_transformation,[],[f42])).
% 8.01/1.49  
% 8.01/1.49  fof(f60,plain,(
% 8.01/1.49    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(sK1(X1,X2),X1) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f34])).
% 8.01/1.49  
% 8.01/1.49  cnf(c_24,negated_conjecture,
% 8.01/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 8.01/1.49      inference(cnf_transformation,[],[f65]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1294,plain,
% 8.01/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_6,plain,
% 8.01/1.49      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 8.01/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.01/1.49      | ~ l1_pre_topc(X0)
% 8.01/1.49      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 8.01/1.49      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 8.01/1.49      inference(cnf_transformation,[],[f72]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_7,plain,
% 8.01/1.49      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 8.01/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.01/1.49      | ~ l1_pre_topc(X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f51]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_154,plain,
% 8.01/1.49      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.01/1.49      | ~ l1_pre_topc(X0)
% 8.01/1.49      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 8.01/1.49      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 8.01/1.49      inference(global_propositional_subsumption,[status(thm)],[c_6,c_7]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_155,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ l1_pre_topc(X1)
% 8.01/1.49      | ~ v1_pre_topc(k1_pre_topc(X1,X0))
% 8.01/1.49      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_154]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_8,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ l1_pre_topc(X1)
% 8.01/1.49      | v1_pre_topc(k1_pre_topc(X1,X0)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f50]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_160,plain,
% 8.01/1.49      ( ~ l1_pre_topc(X1)
% 8.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_155,c_8]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_161,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ l1_pre_topc(X1)
% 8.01/1.49      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_160]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1292,plain,
% 8.01/1.49      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
% 8.01/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.01/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_161]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1590,plain,
% 8.01/1.49      ( k2_struct_0(k1_pre_topc(sK2,sK3)) = sK3
% 8.01/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1294,c_1292]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_25,negated_conjecture,
% 8.01/1.49      ( l1_pre_topc(sK2) ),
% 8.01/1.49      inference(cnf_transformation,[],[f64]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_26,plain,
% 8.01/1.49      ( l1_pre_topc(sK2) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1793,plain,
% 8.01/1.49      ( k2_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_1590,c_26]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_15,plain,
% 8.01/1.49      ( v2_compts_1(X0,X1)
% 8.01/1.49      | ~ m1_pre_topc(X2,X1)
% 8.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ r1_tarski(X0,k2_struct_0(X2))
% 8.01/1.49      | ~ l1_pre_topc(X1)
% 8.01/1.49      | sK1(X2,X0) = X0 ),
% 8.01/1.49      inference(cnf_transformation,[],[f59]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1297,plain,
% 8.01/1.49      ( sK1(X0,X1) = X1
% 8.01/1.49      | v2_compts_1(X1,X2) = iProver_top
% 8.01/1.49      | m1_pre_topc(X0,X2) != iProver_top
% 8.01/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 8.01/1.49      | r1_tarski(X1,k2_struct_0(X0)) != iProver_top
% 8.01/1.49      | l1_pre_topc(X2) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2835,plain,
% 8.01/1.49      ( sK1(X0,sK3) = sK3
% 8.01/1.49      | v2_compts_1(sK3,sK2) = iProver_top
% 8.01/1.49      | m1_pre_topc(X0,sK2) != iProver_top
% 8.01/1.49      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
% 8.01/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1294,c_1297]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3077,plain,
% 8.01/1.49      ( r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
% 8.01/1.49      | m1_pre_topc(X0,sK2) != iProver_top
% 8.01/1.49      | v2_compts_1(sK3,sK2) = iProver_top
% 8.01/1.49      | sK1(X0,sK3) = sK3 ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_2835,c_26]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3078,plain,
% 8.01/1.49      ( sK1(X0,sK3) = sK3
% 8.01/1.49      | v2_compts_1(sK3,sK2) = iProver_top
% 8.01/1.49      | m1_pre_topc(X0,sK2) != iProver_top
% 8.01/1.49      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_3077]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3083,plain,
% 8.01/1.49      ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
% 8.01/1.49      | v2_compts_1(sK3,sK2) = iProver_top
% 8.01/1.49      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 8.01/1.49      | r1_tarski(sK3,sK3) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1793,c_3078]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_27,plain,
% 8.01/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2,plain,
% 8.01/1.49      ( r1_tarski(X0,X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f70]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1500,plain,
% 8.01/1.49      ( r1_tarski(sK3,sK3) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1501,plain,
% 8.01/1.49      ( r1_tarski(sK3,sK3) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_1500]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1477,plain,
% 8.01/1.49      ( m1_pre_topc(k1_pre_topc(sK2,X0),sK2)
% 8.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 8.01/1.49      | ~ l1_pre_topc(sK2) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1611,plain,
% 8.01/1.49      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
% 8.01/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 8.01/1.49      | ~ l1_pre_topc(sK2) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_1477]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1612,plain,
% 8.01/1.49      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top
% 8.01/1.49      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 8.01/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_1611]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_12,plain,
% 8.01/1.49      ( ~ v2_compts_1(k2_struct_0(X0),X0)
% 8.01/1.49      | v1_compts_1(X0)
% 8.01/1.49      | ~ l1_pre_topc(X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f56]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_18,plain,
% 8.01/1.49      ( ~ sP0(X0,X1)
% 8.01/1.49      | ~ v2_compts_1(X0,X1)
% 8.01/1.49      | ~ v1_compts_1(k1_pre_topc(X1,X0)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f63]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_21,negated_conjecture,
% 8.01/1.49      ( sP0(sK3,sK2)
% 8.01/1.49      | ~ v2_compts_1(sK3,sK2)
% 8.01/1.49      | ~ v1_compts_1(k1_pre_topc(sK2,sK3)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f68]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_388,plain,
% 8.01/1.49      ( ~ v2_compts_1(X0,X1)
% 8.01/1.49      | ~ v2_compts_1(sK3,sK2)
% 8.01/1.49      | ~ v1_compts_1(k1_pre_topc(X1,X0))
% 8.01/1.49      | ~ v1_compts_1(k1_pre_topc(sK2,sK3))
% 8.01/1.49      | sK3 != X0
% 8.01/1.49      | sK2 != X1 ),
% 8.01/1.49      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_389,plain,
% 8.01/1.49      ( ~ v2_compts_1(sK3,sK2) | ~ v1_compts_1(k1_pre_topc(sK2,sK3)) ),
% 8.01/1.49      inference(unflattening,[status(thm)],[c_388]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_408,plain,
% 8.01/1.49      ( ~ v2_compts_1(k2_struct_0(X0),X0)
% 8.01/1.49      | ~ v2_compts_1(sK3,sK2)
% 8.01/1.49      | ~ l1_pre_topc(X0)
% 8.01/1.49      | k1_pre_topc(sK2,sK3) != X0 ),
% 8.01/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_389]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_409,plain,
% 8.01/1.49      ( ~ v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3))
% 8.01/1.49      | ~ v2_compts_1(sK3,sK2)
% 8.01/1.49      | ~ l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
% 8.01/1.49      inference(unflattening,[status(thm)],[c_408]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1291,plain,
% 8.01/1.49      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top
% 8.01/1.49      | v2_compts_1(sK3,sK2) != iProver_top
% 8.01/1.49      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_409]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1796,plain,
% 8.01/1.49      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
% 8.01/1.49      | v2_compts_1(sK3,sK2) != iProver_top
% 8.01/1.49      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 8.01/1.49      inference(demodulation,[status(thm)],[c_1793,c_1291]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_9,plain,
% 8.01/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f52]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1367,plain,
% 8.01/1.49      ( ~ m1_pre_topc(k1_pre_topc(sK2,sK3),X0)
% 8.01/1.49      | ~ l1_pre_topc(X0)
% 8.01/1.49      | l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1368,plain,
% 8.01/1.49      ( m1_pre_topc(k1_pre_topc(sK2,sK3),X0) != iProver_top
% 8.01/1.49      | l1_pre_topc(X0) != iProver_top
% 8.01/1.49      | l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_1367]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1370,plain,
% 8.01/1.49      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 8.01/1.49      | l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top
% 8.01/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_1368]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1892,plain,
% 8.01/1.49      ( v2_compts_1(sK3,sK2) != iProver_top
% 8.01/1.49      | v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_1796,c_26,c_27,c_1370,c_1612]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1893,plain,
% 8.01/1.49      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
% 8.01/1.49      | v2_compts_1(sK3,sK2) != iProver_top ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_1892]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_4,plain,
% 8.01/1.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f47]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1305,plain,
% 8.01/1.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3,plain,
% 8.01/1.49      ( k2_subset_1(X0) = X0 ),
% 8.01/1.49      inference(cnf_transformation,[],[f46]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1308,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 8.01/1.49      inference(light_normalisation,[status(thm)],[c_1305,c_3]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_17,plain,
% 8.01/1.49      ( ~ v2_compts_1(X0,X1)
% 8.01/1.49      | v2_compts_1(X0,X2)
% 8.01/1.49      | ~ m1_pre_topc(X2,X1)
% 8.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 8.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ r1_tarski(X0,k2_struct_0(X2))
% 8.01/1.49      | ~ l1_pre_topc(X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f73]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1295,plain,
% 8.01/1.49      ( v2_compts_1(X0,X1) != iProver_top
% 8.01/1.49      | v2_compts_1(X0,X2) = iProver_top
% 8.01/1.49      | m1_pre_topc(X2,X1) != iProver_top
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.01/1.49      | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
% 8.01/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2181,plain,
% 8.01/1.49      ( v2_compts_1(u1_struct_0(X0),X1) != iProver_top
% 8.01/1.49      | v2_compts_1(u1_struct_0(X0),X0) = iProver_top
% 8.01/1.49      | m1_pre_topc(X0,X1) != iProver_top
% 8.01/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.01/1.49      | r1_tarski(u1_struct_0(X0),k2_struct_0(X0)) != iProver_top
% 8.01/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1308,c_1295]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_11,plain,
% 8.01/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.01/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 8.01/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ l1_pre_topc(X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f54]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1299,plain,
% 8.01/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.01/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.01/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.01/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2294,plain,
% 8.01/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.01/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.01/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1308,c_1299]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_7940,plain,
% 8.01/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.01/1.49      | v2_compts_1(u1_struct_0(X0),X0) = iProver_top
% 8.01/1.49      | v2_compts_1(u1_struct_0(X0),X1) != iProver_top
% 8.01/1.49      | r1_tarski(u1_struct_0(X0),k2_struct_0(X0)) != iProver_top
% 8.01/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_2181,c_2294]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_7941,plain,
% 8.01/1.49      ( v2_compts_1(u1_struct_0(X0),X1) != iProver_top
% 8.01/1.49      | v2_compts_1(u1_struct_0(X0),X0) = iProver_top
% 8.01/1.49      | m1_pre_topc(X0,X1) != iProver_top
% 8.01/1.49      | r1_tarski(u1_struct_0(X0),k2_struct_0(X0)) != iProver_top
% 8.01/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_7940]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_7950,plain,
% 8.01/1.49      ( v2_compts_1(u1_struct_0(k1_pre_topc(sK2,sK3)),X0) != iProver_top
% 8.01/1.49      | v2_compts_1(u1_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
% 8.01/1.49      | m1_pre_topc(k1_pre_topc(sK2,sK3),X0) != iProver_top
% 8.01/1.49      | r1_tarski(u1_struct_0(k1_pre_topc(sK2,sK3)),sK3) != iProver_top
% 8.01/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1793,c_7941]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ l1_pre_topc(X1)
% 8.01/1.49      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 8.01/1.49      inference(cnf_transformation,[],[f53]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1300,plain,
% 8.01/1.49      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
% 8.01/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.01/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1704,plain,
% 8.01/1.49      ( u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3
% 8.01/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1294,c_1300]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1633,plain,
% 8.01/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
% 8.01/1.49      | ~ l1_pre_topc(X0)
% 8.01/1.49      | u1_struct_0(k1_pre_topc(X0,sK3)) = sK3 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1635,plain,
% 8.01/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 8.01/1.49      | ~ l1_pre_topc(sK2)
% 8.01/1.49      | u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_1633]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1800,plain,
% 8.01/1.49      ( u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_1704,c_25,c_24,c_1635]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_7959,plain,
% 8.01/1.49      ( v2_compts_1(sK3,X0) != iProver_top
% 8.01/1.49      | v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
% 8.01/1.49      | m1_pre_topc(k1_pre_topc(sK2,sK3),X0) != iProver_top
% 8.01/1.49      | r1_tarski(sK3,sK3) != iProver_top
% 8.01/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.01/1.49      inference(light_normalisation,[status(thm)],[c_7950,c_1800]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_13,plain,
% 8.01/1.49      ( v2_compts_1(k2_struct_0(X0),X0)
% 8.01/1.49      | ~ v1_compts_1(X0)
% 8.01/1.49      | ~ l1_pre_topc(X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f55]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_19,plain,
% 8.01/1.49      ( ~ sP0(X0,X1)
% 8.01/1.49      | v2_compts_1(X0,X1)
% 8.01/1.49      | v1_compts_1(k1_pre_topc(X1,X0)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f62]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_22,negated_conjecture,
% 8.01/1.49      ( sP0(sK3,sK2)
% 8.01/1.49      | v2_compts_1(sK3,sK2)
% 8.01/1.49      | v1_compts_1(k1_pre_topc(sK2,sK3)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f67]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_361,plain,
% 8.01/1.49      ( v2_compts_1(X0,X1)
% 8.01/1.49      | v2_compts_1(sK3,sK2)
% 8.01/1.49      | v1_compts_1(k1_pre_topc(X1,X0))
% 8.01/1.49      | v1_compts_1(k1_pre_topc(sK2,sK3))
% 8.01/1.49      | sK3 != X0
% 8.01/1.49      | sK2 != X1 ),
% 8.01/1.49      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_362,plain,
% 8.01/1.49      ( v2_compts_1(sK3,sK2) | v1_compts_1(k1_pre_topc(sK2,sK3)) ),
% 8.01/1.49      inference(unflattening,[status(thm)],[c_361]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_421,plain,
% 8.01/1.49      ( v2_compts_1(k2_struct_0(X0),X0)
% 8.01/1.49      | v2_compts_1(sK3,sK2)
% 8.01/1.49      | ~ l1_pre_topc(X0)
% 8.01/1.49      | k1_pre_topc(sK2,sK3) != X0 ),
% 8.01/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_362]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_422,plain,
% 8.01/1.49      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3))
% 8.01/1.49      | v2_compts_1(sK3,sK2)
% 8.01/1.49      | ~ l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
% 8.01/1.49      inference(unflattening,[status(thm)],[c_421]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1290,plain,
% 8.01/1.49      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
% 8.01/1.49      | v2_compts_1(sK3,sK2) = iProver_top
% 8.01/1.49      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1795,plain,
% 8.01/1.49      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
% 8.01/1.49      | v2_compts_1(sK3,sK2) = iProver_top
% 8.01/1.49      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 8.01/1.49      inference(demodulation,[status(thm)],[c_1793,c_1290]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2000,plain,
% 8.01/1.49      ( v2_compts_1(sK3,sK2) = iProver_top
% 8.01/1.49      | v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_1795,c_26,c_27,c_1370,c_1612]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2001,plain,
% 8.01/1.49      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
% 8.01/1.49      | v2_compts_1(sK3,sK2) = iProver_top ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_2000]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_7979,plain,
% 8.01/1.49      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
% 8.01/1.49      | v2_compts_1(sK3,sK2) != iProver_top
% 8.01/1.49      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 8.01/1.49      | r1_tarski(sK3,sK3) != iProver_top
% 8.01/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_7959]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_8868,plain,
% 8.01/1.49      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_7959,c_26,c_27,c_1501,c_1612,c_2001,c_7979]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_18512,plain,
% 8.01/1.49      ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3 ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_3083,c_26,c_27,c_1501,c_1590,c_1612,c_1689,c_1772,
% 8.01/1.49                 c_1893,c_2001,c_7979]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_14,plain,
% 8.01/1.49      ( v2_compts_1(X0,X1)
% 8.01/1.49      | ~ v2_compts_1(sK1(X2,X0),X2)
% 8.01/1.49      | ~ m1_pre_topc(X2,X1)
% 8.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ r1_tarski(X0,k2_struct_0(X2))
% 8.01/1.49      | ~ l1_pre_topc(X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f60]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1298,plain,
% 8.01/1.49      ( v2_compts_1(X0,X1) = iProver_top
% 8.01/1.49      | v2_compts_1(sK1(X2,X0),X2) != iProver_top
% 8.01/1.49      | m1_pre_topc(X2,X1) != iProver_top
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.01/1.49      | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
% 8.01/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2854,plain,
% 8.01/1.49      ( v2_compts_1(sK1(X0,sK3),X0) != iProver_top
% 8.01/1.49      | v2_compts_1(sK3,sK2) = iProver_top
% 8.01/1.49      | m1_pre_topc(X0,sK2) != iProver_top
% 8.01/1.49      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
% 8.01/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1294,c_1298]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2955,plain,
% 8.01/1.49      ( r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
% 8.01/1.49      | m1_pre_topc(X0,sK2) != iProver_top
% 8.01/1.49      | v2_compts_1(sK3,sK2) = iProver_top
% 8.01/1.49      | v2_compts_1(sK1(X0,sK3),X0) != iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_2854,c_26]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2956,plain,
% 8.01/1.49      ( v2_compts_1(sK1(X0,sK3),X0) != iProver_top
% 8.01/1.49      | v2_compts_1(sK3,sK2) = iProver_top
% 8.01/1.49      | m1_pre_topc(X0,sK2) != iProver_top
% 8.01/1.49      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_2955]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_18523,plain,
% 8.01/1.49      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
% 8.01/1.49      | v2_compts_1(sK3,sK2) = iProver_top
% 8.01/1.49      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 8.01/1.49      | r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_18512,c_2956]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_18525,plain,
% 8.01/1.49      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
% 8.01/1.49      | v2_compts_1(sK3,sK2) = iProver_top
% 8.01/1.49      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 8.01/1.49      | r1_tarski(sK3,sK3) != iProver_top ),
% 8.01/1.49      inference(light_normalisation,[status(thm)],[c_18523,c_1793]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(contradiction,plain,
% 8.01/1.49      ( $false ),
% 8.01/1.49      inference(minisat,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_18525,c_8868,c_1893,c_1612,c_1501,c_27,c_26]) ).
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.01/1.49  
% 8.01/1.49  ------                               Statistics
% 8.01/1.49  
% 8.01/1.49  ------ General
% 8.01/1.49  
% 8.01/1.49  abstr_ref_over_cycles:                  0
% 8.01/1.49  abstr_ref_under_cycles:                 0
% 8.01/1.49  gc_basic_clause_elim:                   0
% 8.01/1.49  forced_gc_time:                         0
% 8.01/1.49  parsing_time:                           0.014
% 8.01/1.49  unif_index_cands_time:                  0.
% 8.01/1.49  unif_index_add_time:                    0.
% 8.01/1.49  orderings_time:                         0.
% 8.01/1.49  out_proof_time:                         0.019
% 8.01/1.49  total_time:                             0.94
% 8.01/1.49  num_of_symbols:                         48
% 8.01/1.49  num_of_terms:                           19058
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing
% 8.01/1.49  
% 8.01/1.49  num_of_splits:                          0
% 8.01/1.49  num_of_split_atoms:                     0
% 8.01/1.49  num_of_reused_defs:                     0
% 8.01/1.49  num_eq_ax_congr_red:                    15
% 8.01/1.49  num_of_sem_filtered_clauses:            1
% 8.01/1.49  num_of_subtypes:                        0
% 8.01/1.49  monotx_restored_types:                  0
% 8.01/1.49  sat_num_of_epr_types:                   0
% 8.01/1.49  sat_num_of_non_cyclic_types:            0
% 8.01/1.49  sat_guarded_non_collapsed_types:        0
% 8.01/1.49  num_pure_diseq_elim:                    0
% 8.01/1.49  simp_replaced_by:                       0
% 8.01/1.49  res_preprocessed:                       110
% 8.01/1.49  prep_upred:                             0
% 8.01/1.49  prep_unflattend:                        50
% 8.01/1.49  smt_new_axioms:                         0
% 8.01/1.49  pred_elim_cands:                        6
% 8.01/1.49  pred_elim:                              2
% 8.01/1.49  pred_elim_cl:                           5
% 8.01/1.49  pred_elim_cycles:                       6
% 8.01/1.49  merged_defs:                            0
% 8.01/1.49  merged_defs_ncl:                        0
% 8.01/1.49  bin_hyper_res:                          0
% 8.01/1.49  prep_cycles:                            4
% 8.01/1.49  pred_elim_time:                         0.011
% 8.01/1.49  splitting_time:                         0.
% 8.01/1.49  sem_filter_time:                        0.
% 8.01/1.49  monotx_time:                            0.
% 8.01/1.49  subtype_inf_time:                       0.
% 8.01/1.49  
% 8.01/1.49  ------ Problem properties
% 8.01/1.49  
% 8.01/1.49  clauses:                                20
% 8.01/1.49  conjectures:                            2
% 8.01/1.49  epr:                                    5
% 8.01/1.49  horn:                                   17
% 8.01/1.49  ground:                                 5
% 8.01/1.49  unary:                                  5
% 8.01/1.49  binary:                                 1
% 8.01/1.49  lits:                                   65
% 8.01/1.49  lits_eq:                                8
% 8.01/1.49  fd_pure:                                0
% 8.01/1.49  fd_pseudo:                              0
% 8.01/1.49  fd_cond:                                0
% 8.01/1.49  fd_pseudo_cond:                         1
% 8.01/1.49  ac_symbols:                             0
% 8.01/1.49  
% 8.01/1.49  ------ Propositional Solver
% 8.01/1.49  
% 8.01/1.49  prop_solver_calls:                      34
% 8.01/1.49  prop_fast_solver_calls:                 1929
% 8.01/1.49  smt_solver_calls:                       0
% 8.01/1.49  smt_fast_solver_calls:                  0
% 8.01/1.49  prop_num_of_clauses:                    8769
% 8.01/1.49  prop_preprocess_simplified:             17994
% 8.01/1.49  prop_fo_subsumed:                       139
% 8.01/1.49  prop_solver_time:                       0.
% 8.01/1.49  smt_solver_time:                        0.
% 8.01/1.49  smt_fast_solver_time:                   0.
% 8.01/1.49  prop_fast_solver_time:                  0.
% 8.01/1.49  prop_unsat_core_time:                   0.001
% 8.01/1.49  
% 8.01/1.49  ------ QBF
% 8.01/1.49  
% 8.01/1.49  qbf_q_res:                              0
% 8.01/1.49  qbf_num_tautologies:                    0
% 8.01/1.49  qbf_prep_cycles:                        0
% 8.01/1.49  
% 8.01/1.49  ------ BMC1
% 8.01/1.49  
% 8.01/1.49  bmc1_current_bound:                     -1
% 8.01/1.49  bmc1_last_solved_bound:                 -1
% 8.01/1.49  bmc1_unsat_core_size:                   -1
% 8.01/1.49  bmc1_unsat_core_parents_size:           -1
% 8.01/1.49  bmc1_merge_next_fun:                    0
% 8.01/1.49  bmc1_unsat_core_clauses_time:           0.
% 8.01/1.49  
% 8.01/1.49  ------ Instantiation
% 8.01/1.49  
% 8.01/1.49  inst_num_of_clauses:                    2377
% 8.01/1.49  inst_num_in_passive:                    879
% 8.01/1.49  inst_num_in_active:                     977
% 8.01/1.49  inst_num_in_unprocessed:                521
% 8.01/1.49  inst_num_of_loops:                      1040
% 8.01/1.49  inst_num_of_learning_restarts:          0
% 8.01/1.49  inst_num_moves_active_passive:          58
% 8.01/1.49  inst_lit_activity:                      0
% 8.01/1.49  inst_lit_activity_moves:                0
% 8.01/1.49  inst_num_tautologies:                   0
% 8.01/1.49  inst_num_prop_implied:                  0
% 8.01/1.49  inst_num_existing_simplified:           0
% 8.01/1.49  inst_num_eq_res_simplified:             0
% 8.01/1.49  inst_num_child_elim:                    0
% 8.01/1.49  inst_num_of_dismatching_blockings:      1662
% 8.01/1.49  inst_num_of_non_proper_insts:           2901
% 8.01/1.49  inst_num_of_duplicates:                 0
% 8.01/1.49  inst_inst_num_from_inst_to_res:         0
% 8.01/1.49  inst_dismatching_checking_time:         0.
% 8.01/1.49  
% 8.01/1.49  ------ Resolution
% 8.01/1.49  
% 8.01/1.49  res_num_of_clauses:                     0
% 8.01/1.49  res_num_in_passive:                     0
% 8.01/1.49  res_num_in_active:                      0
% 8.01/1.49  res_num_of_loops:                       114
% 8.01/1.49  res_forward_subset_subsumed:            255
% 8.01/1.49  res_backward_subset_subsumed:           4
% 8.01/1.49  res_forward_subsumed:                   0
% 8.01/1.49  res_backward_subsumed:                  0
% 8.01/1.49  res_forward_subsumption_resolution:     1
% 8.01/1.49  res_backward_subsumption_resolution:    0
% 8.01/1.49  res_clause_to_clause_subsumption:       1693
% 8.01/1.49  res_orphan_elimination:                 0
% 8.01/1.49  res_tautology_del:                      352
% 8.01/1.49  res_num_eq_res_simplified:              0
% 8.01/1.49  res_num_sel_changes:                    0
% 8.01/1.49  res_moves_from_active_to_pass:          0
% 8.01/1.49  
% 8.01/1.49  ------ Superposition
% 8.01/1.49  
% 8.01/1.49  sup_time_total:                         0.
% 8.01/1.49  sup_time_generating:                    0.
% 8.01/1.49  sup_time_sim_full:                      0.
% 8.01/1.49  sup_time_sim_immed:                     0.
% 8.01/1.49  
% 8.01/1.49  sup_num_of_clauses:                     610
% 8.01/1.49  sup_num_in_active:                      200
% 8.01/1.49  sup_num_in_passive:                     410
% 8.01/1.49  sup_num_of_loops:                       206
% 8.01/1.49  sup_fw_superposition:                   429
% 8.01/1.49  sup_bw_superposition:                   412
% 8.01/1.49  sup_immediate_simplified:               288
% 8.01/1.49  sup_given_eliminated:                   0
% 8.01/1.49  comparisons_done:                       0
% 8.01/1.49  comparisons_avoided:                    0
% 8.01/1.49  
% 8.01/1.49  ------ Simplifications
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  sim_fw_subset_subsumed:                 43
% 8.01/1.49  sim_bw_subset_subsumed:                 9
% 8.01/1.49  sim_fw_subsumed:                        85
% 8.01/1.49  sim_bw_subsumed:                        10
% 8.01/1.49  sim_fw_subsumption_res:                 0
% 8.01/1.49  sim_bw_subsumption_res:                 0
% 8.01/1.49  sim_tautology_del:                      27
% 8.01/1.49  sim_eq_tautology_del:                   31
% 8.01/1.49  sim_eq_res_simp:                        0
% 8.01/1.49  sim_fw_demodulated:                     0
% 8.01/1.49  sim_bw_demodulated:                     6
% 8.01/1.49  sim_light_normalised:                   175
% 8.01/1.49  sim_joinable_taut:                      0
% 8.01/1.49  sim_joinable_simp:                      0
% 8.01/1.49  sim_ac_normalised:                      0
% 8.01/1.49  sim_smt_subsumption:                    0
% 8.01/1.49  
%------------------------------------------------------------------------------
