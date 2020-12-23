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
% DateTime   : Thu Dec  3 12:17:55 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  176 (3142 expanded)
%              Number of clauses        :  109 ( 918 expanded)
%              Number of leaves         :   15 ( 713 expanded)
%              Depth                    :   29
%              Number of atoms          :  673 (16746 expanded)
%              Number of equality atoms :  285 (3596 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f25,plain,(
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

fof(f26,plain,(
    ! [X1,X0] :
      ( ( ( v2_compts_1(X1,X0)
        <~> v1_compts_1(k1_pre_topc(X0,X1)) )
        & k1_xboole_0 = X1 )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 != X1 )
            | sP0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f25,f26])).

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
    inference(nnf_transformation,[],[f27])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f43,plain,
    ( ( ( ( ~ v1_compts_1(k1_pre_topc(sK2,sK3))
          | ~ v2_compts_1(sK3,sK2) )
        & ( v1_compts_1(k1_pre_topc(sK2,sK3))
          | v2_compts_1(sK3,sK2) )
        & k1_xboole_0 != sK3 )
      | sP0(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).

fof(f64,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(cnf_transformation,[],[f20])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK1(X1,X2),X1)
        & sK1(X1,X2) = X2
        & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | sK1(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ~ v2_compts_1(k2_struct_0(X0),X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_compts_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
          | ~ v2_compts_1(X1,X0) )
        & ( v1_compts_1(k1_pre_topc(X0,X1))
          | v2_compts_1(X1,X0) )
        & k1_xboole_0 = X1 )
      | ~ sP0(X1,X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
          | ~ v2_compts_1(X1,X0) )
        & ( v1_compts_1(k1_pre_topc(X0,X1))
          | v2_compts_1(X1,X0) )
        & k1_xboole_0 = X1 )
      | ~ sP0(X1,X0) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X1,X0))
          | ~ v2_compts_1(X0,X1) )
        & ( v1_compts_1(k1_pre_topc(X1,X0))
          | v2_compts_1(X0,X1) )
        & k1_xboole_0 = X0 )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f37])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(k1_pre_topc(X1,X0))
      | ~ v2_compts_1(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK2,sK3))
    | ~ v2_compts_1(sK3,sK2)
    | sP0(sK3,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(sK1(X1,X2),X1)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    ! [X0] :
      ( v2_compts_1(k2_struct_0(X0),X0)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X1,X0))
      | v2_compts_1(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,
    ( v1_compts_1(k1_pre_topc(sK2,sK3))
    | v2_compts_1(sK3,sK2)
    | sP0(sK3,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1392,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_323,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_7,c_5])).

cnf(c_1391,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_1705,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_1392,c_1391])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1393,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1991,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1705,c_1393])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1399,plain,
    ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2474,plain,
    ( u1_struct_0(k1_pre_topc(sK2,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_1399])).

cnf(c_25,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2844,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | u1_struct_0(k1_pre_topc(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2474,c_25])).

cnf(c_2845,plain,
    ( u1_struct_0(k1_pre_topc(sK2,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2844])).

cnf(c_2853,plain,
    ( u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_1991,c_2845])).

cnf(c_15,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1395,plain,
    ( v2_compts_1(X0,X1) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK1(X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1713,plain,
    ( v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(sK1(X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1393,c_1395])).

cnf(c_2095,plain,
    ( r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
    | m1_subset_1(sK1(X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1713,c_25])).

cnf(c_2096,plain,
    ( v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(sK1(X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2095])).

cnf(c_2969,plain,
    ( v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(sK1(k1_pre_topc(sK2,sK3),sK3),k1_zfmisc_1(sK3)) = iProver_top
    | r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2853,c_2096])).

cnf(c_26,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1583,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1584,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1583])).

cnf(c_4003,plain,
    ( v2_compts_1(sK3,sK2) = iProver_top
    | m1_subset_1(sK1(k1_pre_topc(sK2,sK3),sK3),k1_zfmisc_1(sK3)) = iProver_top
    | r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2969,c_25,c_26,c_1584])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1402,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4010,plain,
    ( v2_compts_1(sK3,sK2) = iProver_top
    | r1_tarski(sK1(k1_pre_topc(sK2,sK3),sK3),sK3) = iProver_top
    | r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4003,c_1402])).

cnf(c_1401,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2591,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_1401])).

cnf(c_3080,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,X0),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2591,c_25])).

cnf(c_3081,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3080])).

cnf(c_3089,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1991,c_3081])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1400,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3191,plain,
    ( l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3089,c_1400])).

cnf(c_1561,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK2,sK3),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1562,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1561])).

cnf(c_1564,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1562])).

cnf(c_3810,plain,
    ( l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3191,c_25,c_26,c_1564,c_1584])).

cnf(c_3815,plain,
    ( u1_struct_0(k1_pre_topc(sK2,sK3)) = k2_struct_0(k1_pre_topc(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_3810,c_1391])).

cnf(c_3816,plain,
    ( k2_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3815,c_2853])).

cnf(c_10053,plain,
    ( v2_compts_1(sK3,sK2) = iProver_top
    | r1_tarski(sK1(k1_pre_topc(sK2,sK3),sK3),sK3) = iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4010,c_3816])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1404,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10057,plain,
    ( v2_compts_1(sK3,sK2) = iProver_top
    | r1_tarski(sK1(k1_pre_topc(sK2,sK3),sK3),sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10053,c_1404])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1405,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10059,plain,
    ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
    | v2_compts_1(sK3,sK2) = iProver_top
    | r1_tarski(sK3,sK1(k1_pre_topc(sK2,sK3),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10057,c_1405])).

cnf(c_1762,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1765,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1762])).

cnf(c_14,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK1(X2,X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1396,plain,
    ( sK1(X0,X1) = X1
    | v2_compts_1(X1,X2) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | r1_tarski(X1,k2_struct_0(X0)) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2396,plain,
    ( sK1(X0,X1) = X1
    | v2_compts_1(X1,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,k2_struct_0(X0)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_1396])).

cnf(c_4302,plain,
    ( r1_tarski(X1,k2_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_compts_1(X1,sK2) = iProver_top
    | sK1(X0,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2396,c_25])).

cnf(c_4303,plain,
    ( sK1(X0,X1) = X1
    | v2_compts_1(X1,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,k2_struct_0(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4302])).

cnf(c_4314,plain,
    ( sK1(X0,sK3) = sK3
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1991,c_4303])).

cnf(c_6762,plain,
    ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3816,c_4314])).

cnf(c_16,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1394,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1398,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1515,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1394,c_1398])).

cnf(c_3557,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(X0,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2853,c_1515])).

cnf(c_10675,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3557,c_3816])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1403,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10682,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10675,c_1403])).

cnf(c_10687,plain,
    ( v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(X0,sK2) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3089,c_10682])).

cnf(c_10733,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v2_compts_1(X0,sK2) != iProver_top
    | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10687,c_25])).

cnf(c_10734,plain,
    ( v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(X0,sK2) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_10733])).

cnf(c_11,plain,
    ( ~ v2_compts_1(k2_struct_0(X0),X0)
    | v1_compts_1(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1)
    | ~ v2_compts_1(X0,X1)
    | ~ v1_compts_1(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_20,negated_conjecture,
    ( sP0(sK3,sK2)
    | ~ v2_compts_1(sK3,sK2)
    | ~ v1_compts_1(k1_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_411,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK3,sK2)
    | ~ v1_compts_1(k1_pre_topc(X1,X0))
    | ~ v1_compts_1(k1_pre_topc(sK2,sK3))
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_412,plain,
    ( ~ v2_compts_1(sK3,sK2)
    | ~ v1_compts_1(k1_pre_topc(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_431,plain,
    ( ~ v2_compts_1(k2_struct_0(X0),X0)
    | ~ v2_compts_1(sK3,sK2)
    | ~ l1_pre_topc(X0)
    | k1_pre_topc(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_412])).

cnf(c_432,plain,
    ( ~ v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3))
    | ~ v2_compts_1(sK3,sK2)
    | ~ l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_1390,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_433,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_1595,plain,
    ( v2_compts_1(sK3,sK2) != iProver_top
    | v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1390,c_25,c_26,c_433,c_1564,c_1584])).

cnf(c_1596,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1595])).

cnf(c_6742,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3816,c_1596])).

cnf(c_10749,plain,
    ( v2_compts_1(sK3,sK2) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10734,c_6742])).

cnf(c_11263,plain,
    ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10059,c_25,c_26,c_1584,c_1765,c_6762,c_10749])).

cnf(c_13,plain,
    ( v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK1(X2,X0),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1397,plain,
    ( v2_compts_1(X0,X1) = iProver_top
    | v2_compts_1(sK1(X2,X0),X2) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2772,plain,
    ( v2_compts_1(X0,sK2) = iProver_top
    | v2_compts_1(sK1(X1,X0),X1) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X1)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_1397])).

cnf(c_3426,plain,
    ( r1_tarski(X0,k2_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | v2_compts_1(sK1(X1,X0),X1) != iProver_top
    | v2_compts_1(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2772,c_25])).

cnf(c_3427,plain,
    ( v2_compts_1(X0,sK2) = iProver_top
    | v2_compts_1(sK1(X1,X0),X1) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3426])).

cnf(c_3438,plain,
    ( v2_compts_1(sK1(X0,sK3),X0) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1991,c_3427])).

cnf(c_11275,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11263,c_3438])).

cnf(c_11404,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11275,c_3816])).

cnf(c_12,plain,
    ( v2_compts_1(k2_struct_0(X0),X0)
    | ~ v1_compts_1(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1)
    | v2_compts_1(X0,X1)
    | v1_compts_1(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_21,negated_conjecture,
    ( sP0(sK3,sK2)
    | v2_compts_1(sK3,sK2)
    | v1_compts_1(k1_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_384,plain,
    ( v2_compts_1(X0,X1)
    | v2_compts_1(sK3,sK2)
    | v1_compts_1(k1_pre_topc(X1,X0))
    | v1_compts_1(k1_pre_topc(sK2,sK3))
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_385,plain,
    ( v2_compts_1(sK3,sK2)
    | v1_compts_1(k1_pre_topc(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_444,plain,
    ( v2_compts_1(k2_struct_0(X0),X0)
    | v2_compts_1(sK3,sK2)
    | ~ l1_pre_topc(X0)
    | k1_pre_topc(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_385])).

cnf(c_445,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3))
    | v2_compts_1(sK3,sK2)
    | ~ l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_1389,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_446,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_1608,plain,
    ( v2_compts_1(sK3,sK2) = iProver_top
    | v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1389,c_25,c_26,c_446,c_1564,c_1584])).

cnf(c_1609,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_1608])).

cnf(c_6741,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3816,c_1609])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11404,c_10749,c_6741,c_1765,c_1584,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.50/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/0.98  
% 3.50/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.50/0.98  
% 3.50/0.98  ------  iProver source info
% 3.50/0.98  
% 3.50/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.50/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.50/0.98  git: non_committed_changes: false
% 3.50/0.98  git: last_make_outside_of_git: false
% 3.50/0.98  
% 3.50/0.98  ------ 
% 3.50/0.98  
% 3.50/0.98  ------ Input Options
% 3.50/0.98  
% 3.50/0.98  --out_options                           all
% 3.50/0.98  --tptp_safe_out                         true
% 3.50/0.98  --problem_path                          ""
% 3.50/0.98  --include_path                          ""
% 3.50/0.98  --clausifier                            res/vclausify_rel
% 3.50/0.98  --clausifier_options                    --mode clausify
% 3.50/0.98  --stdin                                 false
% 3.50/0.98  --stats_out                             all
% 3.50/0.98  
% 3.50/0.98  ------ General Options
% 3.50/0.98  
% 3.50/0.98  --fof                                   false
% 3.50/0.98  --time_out_real                         305.
% 3.50/0.98  --time_out_virtual                      -1.
% 3.50/0.98  --symbol_type_check                     false
% 3.50/0.98  --clausify_out                          false
% 3.50/0.98  --sig_cnt_out                           false
% 3.50/0.98  --trig_cnt_out                          false
% 3.50/0.98  --trig_cnt_out_tolerance                1.
% 3.50/0.98  --trig_cnt_out_sk_spl                   false
% 3.50/0.98  --abstr_cl_out                          false
% 3.50/0.98  
% 3.50/0.98  ------ Global Options
% 3.50/0.98  
% 3.50/0.98  --schedule                              default
% 3.50/0.98  --add_important_lit                     false
% 3.50/0.98  --prop_solver_per_cl                    1000
% 3.50/0.98  --min_unsat_core                        false
% 3.50/0.98  --soft_assumptions                      false
% 3.50/0.98  --soft_lemma_size                       3
% 3.50/0.98  --prop_impl_unit_size                   0
% 3.50/0.98  --prop_impl_unit                        []
% 3.50/0.98  --share_sel_clauses                     true
% 3.50/0.98  --reset_solvers                         false
% 3.50/0.98  --bc_imp_inh                            [conj_cone]
% 3.50/0.98  --conj_cone_tolerance                   3.
% 3.50/0.98  --extra_neg_conj                        none
% 3.50/0.98  --large_theory_mode                     true
% 3.50/0.98  --prolific_symb_bound                   200
% 3.50/0.98  --lt_threshold                          2000
% 3.50/0.98  --clause_weak_htbl                      true
% 3.50/0.98  --gc_record_bc_elim                     false
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing Options
% 3.50/0.98  
% 3.50/0.98  --preprocessing_flag                    true
% 3.50/0.98  --time_out_prep_mult                    0.1
% 3.50/0.98  --splitting_mode                        input
% 3.50/0.98  --splitting_grd                         true
% 3.50/0.98  --splitting_cvd                         false
% 3.50/0.98  --splitting_cvd_svl                     false
% 3.50/0.98  --splitting_nvd                         32
% 3.50/0.98  --sub_typing                            true
% 3.50/0.98  --prep_gs_sim                           true
% 3.50/0.98  --prep_unflatten                        true
% 3.50/0.98  --prep_res_sim                          true
% 3.50/0.98  --prep_upred                            true
% 3.50/0.98  --prep_sem_filter                       exhaustive
% 3.50/0.98  --prep_sem_filter_out                   false
% 3.50/0.98  --pred_elim                             true
% 3.50/0.98  --res_sim_input                         true
% 3.50/0.98  --eq_ax_congr_red                       true
% 3.50/0.98  --pure_diseq_elim                       true
% 3.50/0.98  --brand_transform                       false
% 3.50/0.98  --non_eq_to_eq                          false
% 3.50/0.98  --prep_def_merge                        true
% 3.50/0.98  --prep_def_merge_prop_impl              false
% 3.50/0.98  --prep_def_merge_mbd                    true
% 3.50/0.98  --prep_def_merge_tr_red                 false
% 3.50/0.98  --prep_def_merge_tr_cl                  false
% 3.50/0.98  --smt_preprocessing                     true
% 3.50/0.98  --smt_ac_axioms                         fast
% 3.50/0.98  --preprocessed_out                      false
% 3.50/0.98  --preprocessed_stats                    false
% 3.50/0.98  
% 3.50/0.98  ------ Abstraction refinement Options
% 3.50/0.98  
% 3.50/0.98  --abstr_ref                             []
% 3.50/0.98  --abstr_ref_prep                        false
% 3.50/0.98  --abstr_ref_until_sat                   false
% 3.50/0.98  --abstr_ref_sig_restrict                funpre
% 3.50/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/0.98  --abstr_ref_under                       []
% 3.50/0.98  
% 3.50/0.98  ------ SAT Options
% 3.50/0.98  
% 3.50/0.98  --sat_mode                              false
% 3.50/0.98  --sat_fm_restart_options                ""
% 3.50/0.98  --sat_gr_def                            false
% 3.50/0.98  --sat_epr_types                         true
% 3.50/0.98  --sat_non_cyclic_types                  false
% 3.50/0.98  --sat_finite_models                     false
% 3.50/0.98  --sat_fm_lemmas                         false
% 3.50/0.98  --sat_fm_prep                           false
% 3.50/0.98  --sat_fm_uc_incr                        true
% 3.50/0.98  --sat_out_model                         small
% 3.50/0.98  --sat_out_clauses                       false
% 3.50/0.98  
% 3.50/0.98  ------ QBF Options
% 3.50/0.98  
% 3.50/0.98  --qbf_mode                              false
% 3.50/0.98  --qbf_elim_univ                         false
% 3.50/0.98  --qbf_dom_inst                          none
% 3.50/0.98  --qbf_dom_pre_inst                      false
% 3.50/0.98  --qbf_sk_in                             false
% 3.50/0.98  --qbf_pred_elim                         true
% 3.50/0.98  --qbf_split                             512
% 3.50/0.98  
% 3.50/0.98  ------ BMC1 Options
% 3.50/0.98  
% 3.50/0.98  --bmc1_incremental                      false
% 3.50/0.98  --bmc1_axioms                           reachable_all
% 3.50/0.98  --bmc1_min_bound                        0
% 3.50/0.98  --bmc1_max_bound                        -1
% 3.50/0.98  --bmc1_max_bound_default                -1
% 3.50/0.98  --bmc1_symbol_reachability              true
% 3.50/0.98  --bmc1_property_lemmas                  false
% 3.50/0.98  --bmc1_k_induction                      false
% 3.50/0.98  --bmc1_non_equiv_states                 false
% 3.50/0.98  --bmc1_deadlock                         false
% 3.50/0.98  --bmc1_ucm                              false
% 3.50/0.98  --bmc1_add_unsat_core                   none
% 3.50/0.98  --bmc1_unsat_core_children              false
% 3.50/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/0.98  --bmc1_out_stat                         full
% 3.50/0.98  --bmc1_ground_init                      false
% 3.50/0.98  --bmc1_pre_inst_next_state              false
% 3.50/0.98  --bmc1_pre_inst_state                   false
% 3.50/0.98  --bmc1_pre_inst_reach_state             false
% 3.50/0.98  --bmc1_out_unsat_core                   false
% 3.50/0.98  --bmc1_aig_witness_out                  false
% 3.50/0.98  --bmc1_verbose                          false
% 3.50/0.98  --bmc1_dump_clauses_tptp                false
% 3.50/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.50/0.98  --bmc1_dump_file                        -
% 3.50/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.50/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.50/0.98  --bmc1_ucm_extend_mode                  1
% 3.50/0.98  --bmc1_ucm_init_mode                    2
% 3.50/0.98  --bmc1_ucm_cone_mode                    none
% 3.50/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.50/0.98  --bmc1_ucm_relax_model                  4
% 3.50/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.50/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/0.98  --bmc1_ucm_layered_model                none
% 3.50/0.98  --bmc1_ucm_max_lemma_size               10
% 3.50/0.98  
% 3.50/0.98  ------ AIG Options
% 3.50/0.98  
% 3.50/0.98  --aig_mode                              false
% 3.50/0.98  
% 3.50/0.98  ------ Instantiation Options
% 3.50/0.98  
% 3.50/0.98  --instantiation_flag                    true
% 3.50/0.98  --inst_sos_flag                         false
% 3.50/0.98  --inst_sos_phase                        true
% 3.50/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/0.98  --inst_lit_sel_side                     num_symb
% 3.50/0.98  --inst_solver_per_active                1400
% 3.50/0.98  --inst_solver_calls_frac                1.
% 3.50/0.98  --inst_passive_queue_type               priority_queues
% 3.50/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/0.98  --inst_passive_queues_freq              [25;2]
% 3.50/0.98  --inst_dismatching                      true
% 3.50/0.98  --inst_eager_unprocessed_to_passive     true
% 3.50/0.98  --inst_prop_sim_given                   true
% 3.50/0.98  --inst_prop_sim_new                     false
% 3.50/0.98  --inst_subs_new                         false
% 3.50/0.98  --inst_eq_res_simp                      false
% 3.50/0.98  --inst_subs_given                       false
% 3.50/0.98  --inst_orphan_elimination               true
% 3.50/0.98  --inst_learning_loop_flag               true
% 3.50/0.98  --inst_learning_start                   3000
% 3.50/0.98  --inst_learning_factor                  2
% 3.50/0.98  --inst_start_prop_sim_after_learn       3
% 3.50/0.98  --inst_sel_renew                        solver
% 3.50/0.98  --inst_lit_activity_flag                true
% 3.50/0.98  --inst_restr_to_given                   false
% 3.50/0.98  --inst_activity_threshold               500
% 3.50/0.98  --inst_out_proof                        true
% 3.50/0.98  
% 3.50/0.98  ------ Resolution Options
% 3.50/0.98  
% 3.50/0.98  --resolution_flag                       true
% 3.50/0.98  --res_lit_sel                           adaptive
% 3.50/0.98  --res_lit_sel_side                      none
% 3.50/0.98  --res_ordering                          kbo
% 3.50/0.98  --res_to_prop_solver                    active
% 3.50/0.98  --res_prop_simpl_new                    false
% 3.50/0.98  --res_prop_simpl_given                  true
% 3.50/0.98  --res_passive_queue_type                priority_queues
% 3.50/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/0.98  --res_passive_queues_freq               [15;5]
% 3.50/0.98  --res_forward_subs                      full
% 3.50/0.98  --res_backward_subs                     full
% 3.50/0.98  --res_forward_subs_resolution           true
% 3.50/0.98  --res_backward_subs_resolution          true
% 3.50/0.98  --res_orphan_elimination                true
% 3.50/0.98  --res_time_limit                        2.
% 3.50/0.98  --res_out_proof                         true
% 3.50/0.98  
% 3.50/0.98  ------ Superposition Options
% 3.50/0.98  
% 3.50/0.98  --superposition_flag                    true
% 3.50/0.98  --sup_passive_queue_type                priority_queues
% 3.50/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.50/0.98  --demod_completeness_check              fast
% 3.50/0.98  --demod_use_ground                      true
% 3.50/0.98  --sup_to_prop_solver                    passive
% 3.50/0.98  --sup_prop_simpl_new                    true
% 3.50/0.98  --sup_prop_simpl_given                  true
% 3.50/0.98  --sup_fun_splitting                     false
% 3.50/0.98  --sup_smt_interval                      50000
% 3.50/0.98  
% 3.50/0.98  ------ Superposition Simplification Setup
% 3.50/0.98  
% 3.50/0.98  --sup_indices_passive                   []
% 3.50/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.98  --sup_full_bw                           [BwDemod]
% 3.50/0.98  --sup_immed_triv                        [TrivRules]
% 3.50/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.98  --sup_immed_bw_main                     []
% 3.50/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.98  
% 3.50/0.98  ------ Combination Options
% 3.50/0.98  
% 3.50/0.98  --comb_res_mult                         3
% 3.50/0.98  --comb_sup_mult                         2
% 3.50/0.98  --comb_inst_mult                        10
% 3.50/0.98  
% 3.50/0.98  ------ Debug Options
% 3.50/0.98  
% 3.50/0.98  --dbg_backtrace                         false
% 3.50/0.98  --dbg_dump_prop_clauses                 false
% 3.50/0.98  --dbg_dump_prop_clauses_file            -
% 3.50/0.98  --dbg_out_stat                          false
% 3.50/0.98  ------ Parsing...
% 3.50/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/0.98  ------ Proving...
% 3.50/0.98  ------ Problem Properties 
% 3.50/0.98  
% 3.50/0.98  
% 3.50/0.98  clauses                                 18
% 3.50/0.98  conjectures                             2
% 3.50/0.98  EPR                                     5
% 3.50/0.98  Horn                                    15
% 3.50/0.98  unary                                   3
% 3.50/0.98  binary                                  4
% 3.50/0.98  lits                                    58
% 3.50/0.98  lits eq                                 6
% 3.50/0.98  fd_pure                                 0
% 3.50/0.98  fd_pseudo                               0
% 3.50/0.98  fd_cond                                 0
% 3.50/0.98  fd_pseudo_cond                          1
% 3.50/0.98  AC symbols                              0
% 3.50/0.98  
% 3.50/0.98  ------ Schedule dynamic 5 is on 
% 3.50/0.98  
% 3.50/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.50/0.98  
% 3.50/0.98  
% 3.50/0.98  ------ 
% 3.50/0.98  Current options:
% 3.50/0.98  ------ 
% 3.50/0.98  
% 3.50/0.98  ------ Input Options
% 3.50/0.98  
% 3.50/0.98  --out_options                           all
% 3.50/0.98  --tptp_safe_out                         true
% 3.50/0.98  --problem_path                          ""
% 3.50/0.98  --include_path                          ""
% 3.50/0.98  --clausifier                            res/vclausify_rel
% 3.50/0.98  --clausifier_options                    --mode clausify
% 3.50/0.98  --stdin                                 false
% 3.50/0.98  --stats_out                             all
% 3.50/0.98  
% 3.50/0.98  ------ General Options
% 3.50/0.98  
% 3.50/0.98  --fof                                   false
% 3.50/0.98  --time_out_real                         305.
% 3.50/0.98  --time_out_virtual                      -1.
% 3.50/0.98  --symbol_type_check                     false
% 3.50/0.98  --clausify_out                          false
% 3.50/0.98  --sig_cnt_out                           false
% 3.50/0.98  --trig_cnt_out                          false
% 3.50/0.98  --trig_cnt_out_tolerance                1.
% 3.50/0.98  --trig_cnt_out_sk_spl                   false
% 3.50/0.98  --abstr_cl_out                          false
% 3.50/0.98  
% 3.50/0.98  ------ Global Options
% 3.50/0.98  
% 3.50/0.98  --schedule                              default
% 3.50/0.98  --add_important_lit                     false
% 3.50/0.98  --prop_solver_per_cl                    1000
% 3.50/0.98  --min_unsat_core                        false
% 3.50/0.98  --soft_assumptions                      false
% 3.50/0.98  --soft_lemma_size                       3
% 3.50/0.98  --prop_impl_unit_size                   0
% 3.50/0.98  --prop_impl_unit                        []
% 3.50/0.98  --share_sel_clauses                     true
% 3.50/0.98  --reset_solvers                         false
% 3.50/0.98  --bc_imp_inh                            [conj_cone]
% 3.50/0.98  --conj_cone_tolerance                   3.
% 3.50/0.98  --extra_neg_conj                        none
% 3.50/0.98  --large_theory_mode                     true
% 3.50/0.98  --prolific_symb_bound                   200
% 3.50/0.98  --lt_threshold                          2000
% 3.50/0.98  --clause_weak_htbl                      true
% 3.50/0.98  --gc_record_bc_elim                     false
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing Options
% 3.50/0.98  
% 3.50/0.98  --preprocessing_flag                    true
% 3.50/0.98  --time_out_prep_mult                    0.1
% 3.50/0.98  --splitting_mode                        input
% 3.50/0.98  --splitting_grd                         true
% 3.50/0.98  --splitting_cvd                         false
% 3.50/0.98  --splitting_cvd_svl                     false
% 3.50/0.98  --splitting_nvd                         32
% 3.50/0.98  --sub_typing                            true
% 3.50/0.98  --prep_gs_sim                           true
% 3.50/0.98  --prep_unflatten                        true
% 3.50/0.98  --prep_res_sim                          true
% 3.50/0.98  --prep_upred                            true
% 3.50/0.98  --prep_sem_filter                       exhaustive
% 3.50/0.98  --prep_sem_filter_out                   false
% 3.50/0.98  --pred_elim                             true
% 3.50/0.98  --res_sim_input                         true
% 3.50/0.98  --eq_ax_congr_red                       true
% 3.50/0.98  --pure_diseq_elim                       true
% 3.50/0.98  --brand_transform                       false
% 3.50/0.98  --non_eq_to_eq                          false
% 3.50/0.98  --prep_def_merge                        true
% 3.50/0.98  --prep_def_merge_prop_impl              false
% 3.50/0.98  --prep_def_merge_mbd                    true
% 3.50/0.98  --prep_def_merge_tr_red                 false
% 3.50/0.98  --prep_def_merge_tr_cl                  false
% 3.50/0.98  --smt_preprocessing                     true
% 3.50/0.98  --smt_ac_axioms                         fast
% 3.50/0.98  --preprocessed_out                      false
% 3.50/0.98  --preprocessed_stats                    false
% 3.50/0.98  
% 3.50/0.98  ------ Abstraction refinement Options
% 3.50/0.98  
% 3.50/0.98  --abstr_ref                             []
% 3.50/0.98  --abstr_ref_prep                        false
% 3.50/0.98  --abstr_ref_until_sat                   false
% 3.50/0.98  --abstr_ref_sig_restrict                funpre
% 3.50/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/0.98  --abstr_ref_under                       []
% 3.50/0.98  
% 3.50/0.98  ------ SAT Options
% 3.50/0.98  
% 3.50/0.98  --sat_mode                              false
% 3.50/0.98  --sat_fm_restart_options                ""
% 3.50/0.98  --sat_gr_def                            false
% 3.50/0.98  --sat_epr_types                         true
% 3.50/0.98  --sat_non_cyclic_types                  false
% 3.50/0.98  --sat_finite_models                     false
% 3.50/0.98  --sat_fm_lemmas                         false
% 3.50/0.98  --sat_fm_prep                           false
% 3.50/0.98  --sat_fm_uc_incr                        true
% 3.50/0.98  --sat_out_model                         small
% 3.50/0.98  --sat_out_clauses                       false
% 3.50/0.98  
% 3.50/0.98  ------ QBF Options
% 3.50/0.98  
% 3.50/0.98  --qbf_mode                              false
% 3.50/0.98  --qbf_elim_univ                         false
% 3.50/0.98  --qbf_dom_inst                          none
% 3.50/0.98  --qbf_dom_pre_inst                      false
% 3.50/0.98  --qbf_sk_in                             false
% 3.50/0.98  --qbf_pred_elim                         true
% 3.50/0.98  --qbf_split                             512
% 3.50/0.98  
% 3.50/0.98  ------ BMC1 Options
% 3.50/0.98  
% 3.50/0.98  --bmc1_incremental                      false
% 3.50/0.98  --bmc1_axioms                           reachable_all
% 3.50/0.98  --bmc1_min_bound                        0
% 3.50/0.98  --bmc1_max_bound                        -1
% 3.50/0.98  --bmc1_max_bound_default                -1
% 3.50/0.98  --bmc1_symbol_reachability              true
% 3.50/0.98  --bmc1_property_lemmas                  false
% 3.50/0.98  --bmc1_k_induction                      false
% 3.50/0.98  --bmc1_non_equiv_states                 false
% 3.50/0.98  --bmc1_deadlock                         false
% 3.50/0.98  --bmc1_ucm                              false
% 3.50/0.98  --bmc1_add_unsat_core                   none
% 3.50/0.98  --bmc1_unsat_core_children              false
% 3.50/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/0.98  --bmc1_out_stat                         full
% 3.50/0.98  --bmc1_ground_init                      false
% 3.50/0.98  --bmc1_pre_inst_next_state              false
% 3.50/0.98  --bmc1_pre_inst_state                   false
% 3.50/0.98  --bmc1_pre_inst_reach_state             false
% 3.50/0.98  --bmc1_out_unsat_core                   false
% 3.50/0.98  --bmc1_aig_witness_out                  false
% 3.50/0.98  --bmc1_verbose                          false
% 3.50/0.98  --bmc1_dump_clauses_tptp                false
% 3.50/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.50/0.98  --bmc1_dump_file                        -
% 3.50/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.50/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.50/0.98  --bmc1_ucm_extend_mode                  1
% 3.50/0.98  --bmc1_ucm_init_mode                    2
% 3.50/0.98  --bmc1_ucm_cone_mode                    none
% 3.50/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.50/0.98  --bmc1_ucm_relax_model                  4
% 3.50/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.50/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/0.98  --bmc1_ucm_layered_model                none
% 3.50/0.98  --bmc1_ucm_max_lemma_size               10
% 3.50/0.98  
% 3.50/0.98  ------ AIG Options
% 3.50/0.98  
% 3.50/0.98  --aig_mode                              false
% 3.50/0.98  
% 3.50/0.98  ------ Instantiation Options
% 3.50/0.98  
% 3.50/0.98  --instantiation_flag                    true
% 3.50/0.98  --inst_sos_flag                         false
% 3.50/0.98  --inst_sos_phase                        true
% 3.50/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/0.98  --inst_lit_sel_side                     none
% 3.50/0.98  --inst_solver_per_active                1400
% 3.50/0.98  --inst_solver_calls_frac                1.
% 3.50/0.98  --inst_passive_queue_type               priority_queues
% 3.50/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/0.99  --inst_passive_queues_freq              [25;2]
% 3.50/0.99  --inst_dismatching                      true
% 3.50/0.99  --inst_eager_unprocessed_to_passive     true
% 3.50/0.99  --inst_prop_sim_given                   true
% 3.50/0.99  --inst_prop_sim_new                     false
% 3.50/0.99  --inst_subs_new                         false
% 3.50/0.99  --inst_eq_res_simp                      false
% 3.50/0.99  --inst_subs_given                       false
% 3.50/0.99  --inst_orphan_elimination               true
% 3.50/0.99  --inst_learning_loop_flag               true
% 3.50/0.99  --inst_learning_start                   3000
% 3.50/0.99  --inst_learning_factor                  2
% 3.50/0.99  --inst_start_prop_sim_after_learn       3
% 3.50/0.99  --inst_sel_renew                        solver
% 3.50/0.99  --inst_lit_activity_flag                true
% 3.50/0.99  --inst_restr_to_given                   false
% 3.50/0.99  --inst_activity_threshold               500
% 3.50/0.99  --inst_out_proof                        true
% 3.50/0.99  
% 3.50/0.99  ------ Resolution Options
% 3.50/0.99  
% 3.50/0.99  --resolution_flag                       false
% 3.50/0.99  --res_lit_sel                           adaptive
% 3.50/0.99  --res_lit_sel_side                      none
% 3.50/0.99  --res_ordering                          kbo
% 3.50/0.99  --res_to_prop_solver                    active
% 3.50/0.99  --res_prop_simpl_new                    false
% 3.50/0.99  --res_prop_simpl_given                  true
% 3.50/0.99  --res_passive_queue_type                priority_queues
% 3.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/0.99  --res_passive_queues_freq               [15;5]
% 3.50/0.99  --res_forward_subs                      full
% 3.50/0.99  --res_backward_subs                     full
% 3.50/0.99  --res_forward_subs_resolution           true
% 3.50/0.99  --res_backward_subs_resolution          true
% 3.50/0.99  --res_orphan_elimination                true
% 3.50/0.99  --res_time_limit                        2.
% 3.50/0.99  --res_out_proof                         true
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Options
% 3.50/0.99  
% 3.50/0.99  --superposition_flag                    true
% 3.50/0.99  --sup_passive_queue_type                priority_queues
% 3.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.50/0.99  --demod_completeness_check              fast
% 3.50/0.99  --demod_use_ground                      true
% 3.50/0.99  --sup_to_prop_solver                    passive
% 3.50/0.99  --sup_prop_simpl_new                    true
% 3.50/0.99  --sup_prop_simpl_given                  true
% 3.50/0.99  --sup_fun_splitting                     false
% 3.50/0.99  --sup_smt_interval                      50000
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Simplification Setup
% 3.50/0.99  
% 3.50/0.99  --sup_indices_passive                   []
% 3.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_full_bw                           [BwDemod]
% 3.50/0.99  --sup_immed_triv                        [TrivRules]
% 3.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_immed_bw_main                     []
% 3.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  
% 3.50/0.99  ------ Combination Options
% 3.50/0.99  
% 3.50/0.99  --comb_res_mult                         3
% 3.50/0.99  --comb_sup_mult                         2
% 3.50/0.99  --comb_inst_mult                        10
% 3.50/0.99  
% 3.50/0.99  ------ Debug Options
% 3.50/0.99  
% 3.50/0.99  --dbg_backtrace                         false
% 3.50/0.99  --dbg_dump_prop_clauses                 false
% 3.50/0.99  --dbg_dump_prop_clauses_file            -
% 3.50/0.99  --dbg_out_stat                          false
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  ------ Proving...
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  % SZS status Theorem for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  fof(f11,conjecture,(
% 3.50/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f12,negated_conjecture,(
% 3.50/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 3.50/0.99    inference(negated_conjecture,[],[f11])).
% 3.50/0.99  
% 3.50/0.99  fof(f13,plain,(
% 3.50/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 3.50/0.99    inference(pure_predicate_removal,[],[f12])).
% 3.50/0.99  
% 3.50/0.99  fof(f25,plain,(
% 3.50/0.99    ? [X0] : (? [X1] : ((((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 != X1) | ((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f13])).
% 3.50/0.99  
% 3.50/0.99  fof(f26,plain,(
% 3.50/0.99    ! [X1,X0] : (((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 = X1) | ~sP0(X1,X0))),
% 3.50/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.50/0.99  
% 3.50/0.99  fof(f27,plain,(
% 3.50/0.99    ? [X0] : (? [X1] : ((((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.50/0.99    inference(definition_folding,[],[f25,f26])).
% 3.50/0.99  
% 3.50/0.99  fof(f39,plain,(
% 3.50/0.99    ? [X0] : (? [X1] : (((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0))) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.50/0.99    inference(nnf_transformation,[],[f27])).
% 3.50/0.99  
% 3.50/0.99  fof(f40,plain,(
% 3.50/0.99    ? [X0] : (? [X1] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.50/0.99    inference(flattening,[],[f39])).
% 3.50/0.99  
% 3.50/0.99  fof(f42,plain,(
% 3.50/0.99    ( ! [X0] : (? [X1] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((((~v1_compts_1(k1_pre_topc(X0,sK3)) | ~v2_compts_1(sK3,X0)) & (v1_compts_1(k1_pre_topc(X0,sK3)) | v2_compts_1(sK3,X0)) & k1_xboole_0 != sK3) | sP0(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f41,plain,(
% 3.50/0.99    ? [X0] : (? [X1] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((((~v1_compts_1(k1_pre_topc(sK2,X1)) | ~v2_compts_1(X1,sK2)) & (v1_compts_1(k1_pre_topc(sK2,X1)) | v2_compts_1(X1,sK2)) & k1_xboole_0 != X1) | sP0(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f43,plain,(
% 3.50/0.99    ((((~v1_compts_1(k1_pre_topc(sK2,sK3)) | ~v2_compts_1(sK3,sK2)) & (v1_compts_1(k1_pre_topc(sK2,sK3)) | v2_compts_1(sK3,sK2)) & k1_xboole_0 != sK3) | sP0(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).
% 3.50/0.99  
% 3.50/0.99  fof(f64,plain,(
% 3.50/0.99    l1_pre_topc(sK2)),
% 3.50/0.99    inference(cnf_transformation,[],[f43])).
% 3.50/0.99  
% 3.50/0.99  fof(f5,axiom,(
% 3.50/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f18,plain,(
% 3.50/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f5])).
% 3.50/0.99  
% 3.50/0.99  fof(f51,plain,(
% 3.50/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f18])).
% 3.50/0.99  
% 3.50/0.99  fof(f3,axiom,(
% 3.50/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f15,plain,(
% 3.50/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f3])).
% 3.50/0.99  
% 3.50/0.99  fof(f49,plain,(
% 3.50/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f15])).
% 3.50/0.99  
% 3.50/0.99  fof(f65,plain,(
% 3.50/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.50/0.99    inference(cnf_transformation,[],[f43])).
% 3.50/0.99  
% 3.50/0.99  fof(f7,axiom,(
% 3.50/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f20,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f7])).
% 3.50/0.99  
% 3.50/0.99  fof(f53,plain,(
% 3.50/0.99    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f20])).
% 3.50/0.99  
% 3.50/0.99  fof(f10,axiom,(
% 3.50/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f23,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f10])).
% 3.50/0.99  
% 3.50/0.99  fof(f24,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(flattening,[],[f23])).
% 3.50/0.99  
% 3.50/0.99  fof(f32,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(nnf_transformation,[],[f24])).
% 3.50/0.99  
% 3.50/0.99  fof(f33,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(rectify,[],[f32])).
% 3.50/0.99  
% 3.50/0.99  fof(f34,plain,(
% 3.50/0.99    ! [X2,X1] : (? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v2_compts_1(sK1(X1,X2),X1) & sK1(X1,X2) = X2 & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f35,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | (~v2_compts_1(sK1(X1,X2),X1) & sK1(X1,X2) = X2 & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 3.50/0.99  
% 3.50/0.99  fof(f58,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f35])).
% 3.50/0.99  
% 3.50/0.99  fof(f4,axiom,(
% 3.50/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f14,plain,(
% 3.50/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 3.50/0.99    inference(pure_predicate_removal,[],[f4])).
% 3.50/0.99  
% 3.50/0.99  fof(f16,plain,(
% 3.50/0.99    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.50/0.99    inference(ennf_transformation,[],[f14])).
% 3.50/0.99  
% 3.50/0.99  fof(f17,plain,(
% 3.50/0.99    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(flattening,[],[f16])).
% 3.50/0.99  
% 3.50/0.99  fof(f50,plain,(
% 3.50/0.99    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f17])).
% 3.50/0.99  
% 3.50/0.99  fof(f2,axiom,(
% 3.50/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f30,plain,(
% 3.50/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.50/0.99    inference(nnf_transformation,[],[f2])).
% 3.50/0.99  
% 3.50/0.99  fof(f47,plain,(
% 3.50/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f30])).
% 3.50/0.99  
% 3.50/0.99  fof(f6,axiom,(
% 3.50/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f19,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f6])).
% 3.50/0.99  
% 3.50/0.99  fof(f52,plain,(
% 3.50/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f19])).
% 3.50/0.99  
% 3.50/0.99  fof(f1,axiom,(
% 3.50/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f28,plain,(
% 3.50/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.50/0.99    inference(nnf_transformation,[],[f1])).
% 3.50/0.99  
% 3.50/0.99  fof(f29,plain,(
% 3.50/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.50/0.99    inference(flattening,[],[f28])).
% 3.50/0.99  
% 3.50/0.99  fof(f44,plain,(
% 3.50/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.50/0.99    inference(cnf_transformation,[],[f29])).
% 3.50/0.99  
% 3.50/0.99  fof(f70,plain,(
% 3.50/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.50/0.99    inference(equality_resolution,[],[f44])).
% 3.50/0.99  
% 3.50/0.99  fof(f46,plain,(
% 3.50/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f29])).
% 3.50/0.99  
% 3.50/0.99  fof(f59,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | sK1(X1,X2) = X2 | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f35])).
% 3.50/0.99  
% 3.50/0.99  fof(f57,plain,(
% 3.50/0.99    ( ! [X4,X2,X0,X1] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f35])).
% 3.50/0.99  
% 3.50/0.99  fof(f71,plain,(
% 3.50/0.99    ( ! [X4,X0,X1] : (v2_compts_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X4,X0) | ~r1_tarski(X4,k2_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(equality_resolution,[],[f57])).
% 3.50/0.99  
% 3.50/0.99  fof(f8,axiom,(
% 3.50/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f21,plain,(
% 3.50/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f8])).
% 3.50/0.99  
% 3.50/0.99  fof(f54,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f21])).
% 3.50/0.99  
% 3.50/0.99  fof(f48,plain,(
% 3.50/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f30])).
% 3.50/0.99  
% 3.50/0.99  fof(f9,axiom,(
% 3.50/0.99    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 3.50/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f22,plain,(
% 3.50/0.99    ! [X0] : ((v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f9])).
% 3.50/0.99  
% 3.50/0.99  fof(f31,plain,(
% 3.50/0.99    ! [X0] : (((v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0)) & (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 3.50/0.99    inference(nnf_transformation,[],[f22])).
% 3.50/0.99  
% 3.50/0.99  fof(f56,plain,(
% 3.50/0.99    ( ! [X0] : (v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f31])).
% 3.50/0.99  
% 3.50/0.99  fof(f36,plain,(
% 3.50/0.99    ! [X1,X0] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0))) & k1_xboole_0 = X1) | ~sP0(X1,X0))),
% 3.50/0.99    inference(nnf_transformation,[],[f26])).
% 3.50/0.99  
% 3.50/0.99  fof(f37,plain,(
% 3.50/0.99    ! [X1,X0] : (((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 = X1) | ~sP0(X1,X0))),
% 3.50/0.99    inference(flattening,[],[f36])).
% 3.50/0.99  
% 3.50/0.99  fof(f38,plain,(
% 3.50/0.99    ! [X0,X1] : (((~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1)) & (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1)) & k1_xboole_0 = X0) | ~sP0(X0,X1))),
% 3.50/0.99    inference(rectify,[],[f37])).
% 3.50/0.99  
% 3.50/0.99  fof(f63,plain,(
% 3.50/0.99    ( ! [X0,X1] : (~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1) | ~sP0(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f38])).
% 3.50/0.99  
% 3.50/0.99  fof(f68,plain,(
% 3.50/0.99    ~v1_compts_1(k1_pre_topc(sK2,sK3)) | ~v2_compts_1(sK3,sK2) | sP0(sK3,sK2)),
% 3.50/0.99    inference(cnf_transformation,[],[f43])).
% 3.50/0.99  
% 3.50/0.99  fof(f60,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(sK1(X1,X2),X1) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f35])).
% 3.50/0.99  
% 3.50/0.99  fof(f55,plain,(
% 3.50/0.99    ( ! [X0] : (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f31])).
% 3.50/0.99  
% 3.50/0.99  fof(f62,plain,(
% 3.50/0.99    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1) | ~sP0(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f38])).
% 3.50/0.99  
% 3.50/0.99  fof(f67,plain,(
% 3.50/0.99    v1_compts_1(k1_pre_topc(sK2,sK3)) | v2_compts_1(sK3,sK2) | sP0(sK3,sK2)),
% 3.50/0.99    inference(cnf_transformation,[],[f43])).
% 3.50/0.99  
% 3.50/0.99  cnf(c_24,negated_conjecture,
% 3.50/0.99      ( l1_pre_topc(sK2) ),
% 3.50/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1392,plain,
% 3.50/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7,plain,
% 3.50/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_5,plain,
% 3.50/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_323,plain,
% 3.50/0.99      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.50/0.99      inference(resolution,[status(thm)],[c_7,c_5]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1391,plain,
% 3.50/0.99      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.50/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1705,plain,
% 3.50/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1392,c_1391]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_23,negated_conjecture,
% 3.50/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1393,plain,
% 3.50/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1991,plain,
% 3.50/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_1705,c_1393]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | ~ l1_pre_topc(X1)
% 3.50/0.99      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1399,plain,
% 3.50/0.99      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
% 3.50/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.50/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2474,plain,
% 3.50/0.99      ( u1_struct_0(k1_pre_topc(sK2,X0)) = X0
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 3.50/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1705,c_1399]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_25,plain,
% 3.50/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2844,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 3.50/0.99      | u1_struct_0(k1_pre_topc(sK2,X0)) = X0 ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_2474,c_25]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2845,plain,
% 3.50/0.99      ( u1_struct_0(k1_pre_topc(sK2,X0)) = X0
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_2844]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2853,plain,
% 3.50/0.99      ( u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1991,c_2845]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_15,plain,
% 3.50/0.99      ( v2_compts_1(X0,X1)
% 3.50/0.99      | ~ m1_pre_topc(X2,X1)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | m1_subset_1(sK1(X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 3.50/0.99      | ~ r1_tarski(X0,k2_struct_0(X2))
% 3.50/0.99      | ~ l1_pre_topc(X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1395,plain,
% 3.50/0.99      ( v2_compts_1(X0,X1) = iProver_top
% 3.50/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.50/0.99      | m1_subset_1(sK1(X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 3.50/0.99      | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
% 3.50/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1713,plain,
% 3.50/0.99      ( v2_compts_1(sK3,sK2) = iProver_top
% 3.50/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.50/0.99      | m1_subset_1(sK1(X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.50/0.99      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
% 3.50/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1393,c_1395]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2095,plain,
% 3.50/0.99      ( r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
% 3.50/0.99      | m1_subset_1(sK1(X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.50/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.50/0.99      | v2_compts_1(sK3,sK2) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_1713,c_25]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2096,plain,
% 3.50/0.99      ( v2_compts_1(sK3,sK2) = iProver_top
% 3.50/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.50/0.99      | m1_subset_1(sK1(X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.50/0.99      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_2095]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2969,plain,
% 3.50/0.99      ( v2_compts_1(sK3,sK2) = iProver_top
% 3.50/0.99      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 3.50/0.99      | m1_subset_1(sK1(k1_pre_topc(sK2,sK3),sK3),k1_zfmisc_1(sK3)) = iProver_top
% 3.50/0.99      | r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_2853,c_2096]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_26,plain,
% 3.50/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6,plain,
% 3.50/0.99      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 3.50/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.50/0.99      | ~ l1_pre_topc(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1583,plain,
% 3.50/0.99      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
% 3.50/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.50/0.99      | ~ l1_pre_topc(sK2) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1584,plain,
% 3.50/0.99      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top
% 3.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.50/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1583]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4003,plain,
% 3.50/0.99      ( v2_compts_1(sK3,sK2) = iProver_top
% 3.50/0.99      | m1_subset_1(sK1(k1_pre_topc(sK2,sK3),sK3),k1_zfmisc_1(sK3)) = iProver_top
% 3.50/0.99      | r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_2969,c_25,c_26,c_1584]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1402,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.50/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4010,plain,
% 3.50/0.99      ( v2_compts_1(sK3,sK2) = iProver_top
% 3.50/0.99      | r1_tarski(sK1(k1_pre_topc(sK2,sK3),sK3),sK3) = iProver_top
% 3.50/0.99      | r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_4003,c_1402]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1401,plain,
% 3.50/0.99      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 3.50/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.50/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2591,plain,
% 3.50/0.99      ( m1_pre_topc(k1_pre_topc(sK2,X0),sK2) = iProver_top
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 3.50/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1705,c_1401]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3080,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 3.50/0.99      | m1_pre_topc(k1_pre_topc(sK2,X0),sK2) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_2591,c_25]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3081,plain,
% 3.50/0.99      ( m1_pre_topc(k1_pre_topc(sK2,X0),sK2) = iProver_top
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_3080]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3089,plain,
% 3.50/0.99      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1991,c_3081]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8,plain,
% 3.50/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1400,plain,
% 3.50/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.50/0.99      | l1_pre_topc(X1) != iProver_top
% 3.50/0.99      | l1_pre_topc(X0) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3191,plain,
% 3.50/0.99      ( l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top
% 3.50/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_3089,c_1400]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1561,plain,
% 3.50/0.99      ( ~ m1_pre_topc(k1_pre_topc(sK2,sK3),X0)
% 3.50/0.99      | ~ l1_pre_topc(X0)
% 3.50/0.99      | l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1562,plain,
% 3.50/0.99      ( m1_pre_topc(k1_pre_topc(sK2,sK3),X0) != iProver_top
% 3.50/0.99      | l1_pre_topc(X0) != iProver_top
% 3.50/0.99      | l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1561]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1564,plain,
% 3.50/0.99      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 3.50/0.99      | l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top
% 3.50/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1562]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3810,plain,
% 3.50/0.99      ( l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_3191,c_25,c_26,c_1564,c_1584]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3815,plain,
% 3.50/0.99      ( u1_struct_0(k1_pre_topc(sK2,sK3)) = k2_struct_0(k1_pre_topc(sK2,sK3)) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_3810,c_1391]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3816,plain,
% 3.50/0.99      ( k2_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_3815,c_2853]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10053,plain,
% 3.50/0.99      ( v2_compts_1(sK3,sK2) = iProver_top
% 3.50/0.99      | r1_tarski(sK1(k1_pre_topc(sK2,sK3),sK3),sK3) = iProver_top
% 3.50/0.99      | r1_tarski(sK3,sK3) != iProver_top ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_4010,c_3816]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2,plain,
% 3.50/0.99      ( r1_tarski(X0,X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1404,plain,
% 3.50/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10057,plain,
% 3.50/0.99      ( v2_compts_1(sK3,sK2) = iProver_top
% 3.50/0.99      | r1_tarski(sK1(k1_pre_topc(sK2,sK3),sK3),sK3) = iProver_top ),
% 3.50/0.99      inference(forward_subsumption_resolution,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_10053,c_1404]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_0,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.50/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1405,plain,
% 3.50/0.99      ( X0 = X1
% 3.50/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.50/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10059,plain,
% 3.50/0.99      ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
% 3.50/0.99      | v2_compts_1(sK3,sK2) = iProver_top
% 3.50/0.99      | r1_tarski(sK3,sK1(k1_pre_topc(sK2,sK3),sK3)) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_10057,c_1405]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1762,plain,
% 3.50/0.99      ( r1_tarski(sK3,sK3) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1765,plain,
% 3.50/0.99      ( r1_tarski(sK3,sK3) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1762]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_14,plain,
% 3.50/0.99      ( v2_compts_1(X0,X1)
% 3.50/0.99      | ~ m1_pre_topc(X2,X1)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | ~ r1_tarski(X0,k2_struct_0(X2))
% 3.50/0.99      | ~ l1_pre_topc(X1)
% 3.50/0.99      | sK1(X2,X0) = X0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1396,plain,
% 3.50/0.99      ( sK1(X0,X1) = X1
% 3.50/0.99      | v2_compts_1(X1,X2) = iProver_top
% 3.50/0.99      | m1_pre_topc(X0,X2) != iProver_top
% 3.50/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 3.50/0.99      | r1_tarski(X1,k2_struct_0(X0)) != iProver_top
% 3.50/0.99      | l1_pre_topc(X2) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2396,plain,
% 3.50/0.99      ( sK1(X0,X1) = X1
% 3.50/0.99      | v2_compts_1(X1,sK2) = iProver_top
% 3.50/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.50/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 3.50/0.99      | r1_tarski(X1,k2_struct_0(X0)) != iProver_top
% 3.50/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1705,c_1396]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4302,plain,
% 3.50/0.99      ( r1_tarski(X1,k2_struct_0(X0)) != iProver_top
% 3.50/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 3.50/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.50/0.99      | v2_compts_1(X1,sK2) = iProver_top
% 3.50/0.99      | sK1(X0,X1) = X1 ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_2396,c_25]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4303,plain,
% 3.50/0.99      ( sK1(X0,X1) = X1
% 3.50/0.99      | v2_compts_1(X1,sK2) = iProver_top
% 3.50/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.50/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 3.50/0.99      | r1_tarski(X1,k2_struct_0(X0)) != iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_4302]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4314,plain,
% 3.50/0.99      ( sK1(X0,sK3) = sK3
% 3.50/0.99      | v2_compts_1(sK3,sK2) = iProver_top
% 3.50/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.50/0.99      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1991,c_4303]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6762,plain,
% 3.50/0.99      ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
% 3.50/0.99      | v2_compts_1(sK3,sK2) = iProver_top
% 3.50/0.99      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 3.50/0.99      | r1_tarski(sK3,sK3) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_3816,c_4314]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_16,plain,
% 3.50/0.99      ( ~ v2_compts_1(X0,X1)
% 3.50/0.99      | v2_compts_1(X0,X2)
% 3.50/0.99      | ~ m1_pre_topc(X2,X1)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | ~ r1_tarski(X0,k2_struct_0(X2))
% 3.50/0.99      | ~ l1_pre_topc(X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1394,plain,
% 3.50/0.99      ( v2_compts_1(X0,X1) != iProver_top
% 3.50/0.99      | v2_compts_1(X0,X2) = iProver_top
% 3.50/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.50/0.99      | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
% 3.50/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10,plain,
% 3.50/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.50/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.50/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | ~ l1_pre_topc(X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1398,plain,
% 3.50/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.50/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.50/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.50/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1515,plain,
% 3.50/0.99      ( v2_compts_1(X0,X1) != iProver_top
% 3.50/0.99      | v2_compts_1(X0,X2) = iProver_top
% 3.50/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 3.50/0.99      | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
% 3.50/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.50/0.99      inference(forward_subsumption_resolution,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_1394,c_1398]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3557,plain,
% 3.50/0.99      ( v2_compts_1(X0,X1) != iProver_top
% 3.50/0.99      | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
% 3.50/0.99      | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 3.50/0.99      | r1_tarski(X0,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top
% 3.50/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_2853,c_1515]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10675,plain,
% 3.50/0.99      ( v2_compts_1(X0,X1) != iProver_top
% 3.50/0.99      | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
% 3.50/0.99      | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 3.50/0.99      | r1_tarski(X0,sK3) != iProver_top
% 3.50/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_3557,c_3816]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1403,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.50/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10682,plain,
% 3.50/0.99      ( v2_compts_1(X0,X1) != iProver_top
% 3.50/0.99      | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
% 3.50/0.99      | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
% 3.50/0.99      | r1_tarski(X0,sK3) != iProver_top
% 3.50/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.50/0.99      inference(forward_subsumption_resolution,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_10675,c_1403]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10687,plain,
% 3.50/0.99      ( v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
% 3.50/0.99      | v2_compts_1(X0,sK2) != iProver_top
% 3.50/0.99      | r1_tarski(X0,sK3) != iProver_top
% 3.50/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_3089,c_10682]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10733,plain,
% 3.50/0.99      ( r1_tarski(X0,sK3) != iProver_top
% 3.50/0.99      | v2_compts_1(X0,sK2) != iProver_top
% 3.50/0.99      | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_10687,c_25]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10734,plain,
% 3.50/0.99      ( v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
% 3.50/0.99      | v2_compts_1(X0,sK2) != iProver_top
% 3.50/0.99      | r1_tarski(X0,sK3) != iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_10733]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11,plain,
% 3.50/0.99      ( ~ v2_compts_1(k2_struct_0(X0),X0)
% 3.50/0.99      | v1_compts_1(X0)
% 3.50/0.99      | ~ l1_pre_topc(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_17,plain,
% 3.50/0.99      ( ~ sP0(X0,X1)
% 3.50/0.99      | ~ v2_compts_1(X0,X1)
% 3.50/0.99      | ~ v1_compts_1(k1_pre_topc(X1,X0)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_20,negated_conjecture,
% 3.50/0.99      ( sP0(sK3,sK2)
% 3.50/0.99      | ~ v2_compts_1(sK3,sK2)
% 3.50/0.99      | ~ v1_compts_1(k1_pre_topc(sK2,sK3)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_411,plain,
% 3.50/0.99      ( ~ v2_compts_1(X0,X1)
% 3.50/0.99      | ~ v2_compts_1(sK3,sK2)
% 3.50/0.99      | ~ v1_compts_1(k1_pre_topc(X1,X0))
% 3.50/0.99      | ~ v1_compts_1(k1_pre_topc(sK2,sK3))
% 3.50/0.99      | sK3 != X0
% 3.50/0.99      | sK2 != X1 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_412,plain,
% 3.50/0.99      ( ~ v2_compts_1(sK3,sK2) | ~ v1_compts_1(k1_pre_topc(sK2,sK3)) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_411]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_431,plain,
% 3.50/0.99      ( ~ v2_compts_1(k2_struct_0(X0),X0)
% 3.50/0.99      | ~ v2_compts_1(sK3,sK2)
% 3.50/0.99      | ~ l1_pre_topc(X0)
% 3.50/0.99      | k1_pre_topc(sK2,sK3) != X0 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_412]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_432,plain,
% 3.50/0.99      ( ~ v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3))
% 3.50/0.99      | ~ v2_compts_1(sK3,sK2)
% 3.50/0.99      | ~ l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_431]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1390,plain,
% 3.50/0.99      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top
% 3.50/0.99      | v2_compts_1(sK3,sK2) != iProver_top
% 3.50/0.99      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_432]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_433,plain,
% 3.50/0.99      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top
% 3.50/0.99      | v2_compts_1(sK3,sK2) != iProver_top
% 3.50/0.99      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_432]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1595,plain,
% 3.50/0.99      ( v2_compts_1(sK3,sK2) != iProver_top
% 3.50/0.99      | v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_1390,c_25,c_26,c_433,c_1564,c_1584]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1596,plain,
% 3.50/0.99      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top
% 3.50/0.99      | v2_compts_1(sK3,sK2) != iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_1595]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6742,plain,
% 3.50/0.99      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
% 3.50/0.99      | v2_compts_1(sK3,sK2) != iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_3816,c_1596]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10749,plain,
% 3.50/0.99      ( v2_compts_1(sK3,sK2) != iProver_top
% 3.50/0.99      | r1_tarski(sK3,sK3) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_10734,c_6742]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11263,plain,
% 3.50/0.99      ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3 ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_10059,c_25,c_26,c_1584,c_1765,c_6762,c_10749]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_13,plain,
% 3.50/0.99      ( v2_compts_1(X0,X1)
% 3.50/0.99      | ~ v2_compts_1(sK1(X2,X0),X2)
% 3.50/0.99      | ~ m1_pre_topc(X2,X1)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.50/0.99      | ~ r1_tarski(X0,k2_struct_0(X2))
% 3.50/0.99      | ~ l1_pre_topc(X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1397,plain,
% 3.50/0.99      ( v2_compts_1(X0,X1) = iProver_top
% 3.50/0.99      | v2_compts_1(sK1(X2,X0),X2) != iProver_top
% 3.50/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.50/0.99      | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
% 3.50/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2772,plain,
% 3.50/0.99      ( v2_compts_1(X0,sK2) = iProver_top
% 3.50/0.99      | v2_compts_1(sK1(X1,X0),X1) != iProver_top
% 3.50/0.99      | m1_pre_topc(X1,sK2) != iProver_top
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 3.50/0.99      | r1_tarski(X0,k2_struct_0(X1)) != iProver_top
% 3.50/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1705,c_1397]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3426,plain,
% 3.50/0.99      ( r1_tarski(X0,k2_struct_0(X1)) != iProver_top
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 3.50/0.99      | m1_pre_topc(X1,sK2) != iProver_top
% 3.50/0.99      | v2_compts_1(sK1(X1,X0),X1) != iProver_top
% 3.50/0.99      | v2_compts_1(X0,sK2) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_2772,c_25]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3427,plain,
% 3.50/0.99      ( v2_compts_1(X0,sK2) = iProver_top
% 3.50/0.99      | v2_compts_1(sK1(X1,X0),X1) != iProver_top
% 3.50/0.99      | m1_pre_topc(X1,sK2) != iProver_top
% 3.50/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 3.50/0.99      | r1_tarski(X0,k2_struct_0(X1)) != iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_3426]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3438,plain,
% 3.50/0.99      ( v2_compts_1(sK1(X0,sK3),X0) != iProver_top
% 3.50/0.99      | v2_compts_1(sK3,sK2) = iProver_top
% 3.50/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.50/0.99      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1991,c_3427]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11275,plain,
% 3.50/0.99      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
% 3.50/0.99      | v2_compts_1(sK3,sK2) = iProver_top
% 3.50/0.99      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 3.50/0.99      | r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_11263,c_3438]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11404,plain,
% 3.50/0.99      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
% 3.50/0.99      | v2_compts_1(sK3,sK2) = iProver_top
% 3.50/0.99      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 3.50/0.99      | r1_tarski(sK3,sK3) != iProver_top ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_11275,c_3816]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_12,plain,
% 3.50/0.99      ( v2_compts_1(k2_struct_0(X0),X0)
% 3.50/0.99      | ~ v1_compts_1(X0)
% 3.50/0.99      | ~ l1_pre_topc(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_18,plain,
% 3.50/0.99      ( ~ sP0(X0,X1)
% 3.50/0.99      | v2_compts_1(X0,X1)
% 3.50/0.99      | v1_compts_1(k1_pre_topc(X1,X0)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_21,negated_conjecture,
% 3.50/0.99      ( sP0(sK3,sK2)
% 3.50/0.99      | v2_compts_1(sK3,sK2)
% 3.50/0.99      | v1_compts_1(k1_pre_topc(sK2,sK3)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_384,plain,
% 3.50/0.99      ( v2_compts_1(X0,X1)
% 3.50/0.99      | v2_compts_1(sK3,sK2)
% 3.50/0.99      | v1_compts_1(k1_pre_topc(X1,X0))
% 3.50/0.99      | v1_compts_1(k1_pre_topc(sK2,sK3))
% 3.50/0.99      | sK3 != X0
% 3.50/0.99      | sK2 != X1 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_385,plain,
% 3.50/0.99      ( v2_compts_1(sK3,sK2) | v1_compts_1(k1_pre_topc(sK2,sK3)) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_384]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_444,plain,
% 3.50/0.99      ( v2_compts_1(k2_struct_0(X0),X0)
% 3.50/0.99      | v2_compts_1(sK3,sK2)
% 3.50/0.99      | ~ l1_pre_topc(X0)
% 3.50/0.99      | k1_pre_topc(sK2,sK3) != X0 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_385]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_445,plain,
% 3.50/0.99      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3))
% 3.50/0.99      | v2_compts_1(sK3,sK2)
% 3.50/0.99      | ~ l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_444]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1389,plain,
% 3.50/0.99      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
% 3.50/0.99      | v2_compts_1(sK3,sK2) = iProver_top
% 3.50/0.99      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_446,plain,
% 3.50/0.99      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
% 3.50/0.99      | v2_compts_1(sK3,sK2) = iProver_top
% 3.50/0.99      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1608,plain,
% 3.50/0.99      ( v2_compts_1(sK3,sK2) = iProver_top
% 3.50/0.99      | v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_1389,c_25,c_26,c_446,c_1564,c_1584]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1609,plain,
% 3.50/0.99      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
% 3.50/0.99      | v2_compts_1(sK3,sK2) = iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_1608]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6741,plain,
% 3.50/0.99      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
% 3.50/0.99      | v2_compts_1(sK3,sK2) = iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_3816,c_1609]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(contradiction,plain,
% 3.50/0.99      ( $false ),
% 3.50/0.99      inference(minisat,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_11404,c_10749,c_6741,c_1765,c_1584,c_26,c_25]) ).
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  ------                               Statistics
% 3.50/0.99  
% 3.50/0.99  ------ General
% 3.50/0.99  
% 3.50/0.99  abstr_ref_over_cycles:                  0
% 3.50/0.99  abstr_ref_under_cycles:                 0
% 3.50/0.99  gc_basic_clause_elim:                   0
% 3.50/0.99  forced_gc_time:                         0
% 3.50/0.99  parsing_time:                           0.011
% 3.50/0.99  unif_index_cands_time:                  0.
% 3.50/0.99  unif_index_add_time:                    0.
% 3.50/0.99  orderings_time:                         0.
% 3.50/0.99  out_proof_time:                         0.011
% 3.50/0.99  total_time:                             0.305
% 3.50/0.99  num_of_symbols:                         47
% 3.50/0.99  num_of_terms:                           6579
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing
% 3.50/0.99  
% 3.50/0.99  num_of_splits:                          0
% 3.50/0.99  num_of_split_atoms:                     0
% 3.50/0.99  num_of_reused_defs:                     0
% 3.50/0.99  num_eq_ax_congr_red:                    14
% 3.50/0.99  num_of_sem_filtered_clauses:            1
% 3.50/0.99  num_of_subtypes:                        0
% 3.50/0.99  monotx_restored_types:                  0
% 3.50/0.99  sat_num_of_epr_types:                   0
% 3.50/0.99  sat_num_of_non_cyclic_types:            0
% 3.50/0.99  sat_guarded_non_collapsed_types:        0
% 3.50/0.99  num_pure_diseq_elim:                    0
% 3.50/0.99  simp_replaced_by:                       0
% 3.50/0.99  res_preprocessed:                       101
% 3.50/0.99  prep_upred:                             0
% 3.50/0.99  prep_unflattend:                        44
% 3.50/0.99  smt_new_axioms:                         0
% 3.50/0.99  pred_elim_cands:                        5
% 3.50/0.99  pred_elim:                              3
% 3.50/0.99  pred_elim_cl:                           6
% 3.50/0.99  pred_elim_cycles:                       5
% 3.50/0.99  merged_defs:                            8
% 3.50/0.99  merged_defs_ncl:                        0
% 3.50/0.99  bin_hyper_res:                          8
% 3.50/0.99  prep_cycles:                            4
% 3.50/0.99  pred_elim_time:                         0.008
% 3.50/0.99  splitting_time:                         0.
% 3.50/0.99  sem_filter_time:                        0.
% 3.50/0.99  monotx_time:                            0.001
% 3.50/0.99  subtype_inf_time:                       0.
% 3.50/0.99  
% 3.50/0.99  ------ Problem properties
% 3.50/0.99  
% 3.50/0.99  clauses:                                18
% 3.50/0.99  conjectures:                            2
% 3.50/0.99  epr:                                    5
% 3.50/0.99  horn:                                   15
% 3.50/0.99  ground:                                 5
% 3.50/0.99  unary:                                  3
% 3.50/0.99  binary:                                 4
% 3.50/0.99  lits:                                   58
% 3.50/0.99  lits_eq:                                6
% 3.50/0.99  fd_pure:                                0
% 3.50/0.99  fd_pseudo:                              0
% 3.50/0.99  fd_cond:                                0
% 3.50/0.99  fd_pseudo_cond:                         1
% 3.50/0.99  ac_symbols:                             0
% 3.50/0.99  
% 3.50/0.99  ------ Propositional Solver
% 3.50/0.99  
% 3.50/0.99  prop_solver_calls:                      29
% 3.50/0.99  prop_fast_solver_calls:                 1296
% 3.50/0.99  smt_solver_calls:                       0
% 3.50/0.99  smt_fast_solver_calls:                  0
% 3.50/0.99  prop_num_of_clauses:                    3243
% 3.50/0.99  prop_preprocess_simplified:             6720
% 3.50/0.99  prop_fo_subsumed:                       43
% 3.50/0.99  prop_solver_time:                       0.
% 3.50/0.99  smt_solver_time:                        0.
% 3.50/0.99  smt_fast_solver_time:                   0.
% 3.50/0.99  prop_fast_solver_time:                  0.
% 3.50/0.99  prop_unsat_core_time:                   0.
% 3.50/0.99  
% 3.50/0.99  ------ QBF
% 3.50/0.99  
% 3.50/0.99  qbf_q_res:                              0
% 3.50/0.99  qbf_num_tautologies:                    0
% 3.50/0.99  qbf_prep_cycles:                        0
% 3.50/0.99  
% 3.50/0.99  ------ BMC1
% 3.50/0.99  
% 3.50/0.99  bmc1_current_bound:                     -1
% 3.50/0.99  bmc1_last_solved_bound:                 -1
% 3.50/0.99  bmc1_unsat_core_size:                   -1
% 3.50/0.99  bmc1_unsat_core_parents_size:           -1
% 3.50/0.99  bmc1_merge_next_fun:                    0
% 3.50/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.50/0.99  
% 3.50/0.99  ------ Instantiation
% 3.50/0.99  
% 3.50/0.99  inst_num_of_clauses:                    881
% 3.50/0.99  inst_num_in_passive:                    19
% 3.50/0.99  inst_num_in_active:                     504
% 3.50/0.99  inst_num_in_unprocessed:                358
% 3.50/0.99  inst_num_of_loops:                      540
% 3.50/0.99  inst_num_of_learning_restarts:          0
% 3.50/0.99  inst_num_moves_active_passive:          30
% 3.50/0.99  inst_lit_activity:                      0
% 3.50/0.99  inst_lit_activity_moves:                0
% 3.50/0.99  inst_num_tautologies:                   0
% 3.50/0.99  inst_num_prop_implied:                  0
% 3.50/0.99  inst_num_existing_simplified:           0
% 3.50/0.99  inst_num_eq_res_simplified:             0
% 3.50/0.99  inst_num_child_elim:                    0
% 3.50/0.99  inst_num_of_dismatching_blockings:      810
% 3.50/0.99  inst_num_of_non_proper_insts:           1464
% 3.50/0.99  inst_num_of_duplicates:                 0
% 3.50/0.99  inst_inst_num_from_inst_to_res:         0
% 3.50/0.99  inst_dismatching_checking_time:         0.
% 3.50/0.99  
% 3.50/0.99  ------ Resolution
% 3.50/0.99  
% 3.50/0.99  res_num_of_clauses:                     0
% 3.50/0.99  res_num_in_passive:                     0
% 3.50/0.99  res_num_in_active:                      0
% 3.50/0.99  res_num_of_loops:                       105
% 3.50/0.99  res_forward_subset_subsumed:            156
% 3.50/0.99  res_backward_subset_subsumed:           10
% 3.50/0.99  res_forward_subsumed:                   0
% 3.50/0.99  res_backward_subsumed:                  0
% 3.50/0.99  res_forward_subsumption_resolution:     1
% 3.50/0.99  res_backward_subsumption_resolution:    0
% 3.50/0.99  res_clause_to_clause_subsumption:       1132
% 3.50/0.99  res_orphan_elimination:                 0
% 3.50/0.99  res_tautology_del:                      229
% 3.50/0.99  res_num_eq_res_simplified:              0
% 3.50/0.99  res_num_sel_changes:                    0
% 3.50/0.99  res_moves_from_active_to_pass:          0
% 3.50/0.99  
% 3.50/0.99  ------ Superposition
% 3.50/0.99  
% 3.50/0.99  sup_time_total:                         0.
% 3.50/0.99  sup_time_generating:                    0.
% 3.50/0.99  sup_time_sim_full:                      0.
% 3.50/0.99  sup_time_sim_immed:                     0.
% 3.50/0.99  
% 3.50/0.99  sup_num_of_clauses:                     301
% 3.50/0.99  sup_num_in_active:                      103
% 3.50/0.99  sup_num_in_passive:                     198
% 3.50/0.99  sup_num_of_loops:                       107
% 3.50/0.99  sup_fw_superposition:                   159
% 3.50/0.99  sup_bw_superposition:                   211
% 3.50/0.99  sup_immediate_simplified:               78
% 3.50/0.99  sup_given_eliminated:                   0
% 3.50/0.99  comparisons_done:                       0
% 3.50/0.99  comparisons_avoided:                    0
% 3.50/0.99  
% 3.50/0.99  ------ Simplifications
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  sim_fw_subset_subsumed:                 12
% 3.50/0.99  sim_bw_subset_subsumed:                 2
% 3.50/0.99  sim_fw_subsumed:                        21
% 3.50/0.99  sim_bw_subsumed:                        8
% 3.50/0.99  sim_fw_subsumption_res:                 8
% 3.50/0.99  sim_bw_subsumption_res:                 0
% 3.50/0.99  sim_tautology_del:                      8
% 3.50/0.99  sim_eq_tautology_del:                   4
% 3.50/0.99  sim_eq_res_simp:                        0
% 3.50/0.99  sim_fw_demodulated:                     0
% 3.50/0.99  sim_bw_demodulated:                     5
% 3.50/0.99  sim_light_normalised:                   51
% 3.50/0.99  sim_joinable_taut:                      0
% 3.50/0.99  sim_joinable_simp:                      0
% 3.50/0.99  sim_ac_normalised:                      0
% 3.50/0.99  sim_smt_subsumption:                    0
% 3.50/0.99  
%------------------------------------------------------------------------------
