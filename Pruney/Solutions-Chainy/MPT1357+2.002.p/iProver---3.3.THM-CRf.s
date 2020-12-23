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
% DateTime   : Thu Dec  3 12:17:55 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  170 (2068 expanded)
%              Number of clauses        :  103 ( 548 expanded)
%              Number of leaves         :   14 ( 453 expanded)
%              Depth                    :   29
%              Number of atoms          :  695 (12212 expanded)
%              Number of equality atoms :  271 (2462 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
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
    inference(pure_predicate_removal,[],[f11])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ( ( v2_compts_1(X1,X0)
        <~> v1_compts_1(k1_pre_topc(X0,X1)) )
        & k1_xboole_0 = X1 )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 != X1 )
            | sP0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f23,f24])).

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
    inference(nnf_transformation,[],[f25])).

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

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

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

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

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
    inference(flattening,[],[f13])).

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
    inference(nnf_transformation,[],[f14])).

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

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ~ v2_compts_1(k2_struct_0(X0),X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

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
    inference(nnf_transformation,[],[f24])).

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

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | sK1(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(sK1(X1,X2),X1)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1581,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1587,plain,
    ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2068,plain,
    ( u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1581,c_1587])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1804,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2320,plain,
    ( u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2068,c_25,c_24,c_1804])).

cnf(c_16,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1583,plain,
    ( v2_compts_1(X0,X1) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK1(X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2604,plain,
    ( v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(sK1(X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1581,c_1583])).

cnf(c_26,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3181,plain,
    ( r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
    | m1_subset_1(sK1(X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2604,c_26])).

cnf(c_3182,plain,
    ( v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(sK1(X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3181])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1592,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3192,plain,
    ( v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(sK1(X0,sK3),u1_struct_0(X0)) = iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3182,c_1592])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2032,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2035,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2032])).

cnf(c_7,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1590,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2741,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1581,c_1590])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1800,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1801,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1800])).

cnf(c_3006,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2741,c_26,c_27,c_1801])).

cnf(c_17,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1582,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1586,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1723,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1582,c_1586])).

cnf(c_4452,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(X0,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2320,c_1723])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_158,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_7])).

cnf(c_159,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_158])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_164,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_159,c_8])).

cnf(c_165,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_164])).

cnf(c_1579,plain,
    ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_165])).

cnf(c_1899,plain,
    ( k2_struct_0(k1_pre_topc(sK2,sK3)) = sK3
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1581,c_1579])).

cnf(c_1808,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k2_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_2223,plain,
    ( k2_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1899,c_25,c_24,c_1808])).

cnf(c_4472,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4452,c_2223])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2715,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2716,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK3)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2715])).

cnf(c_6051,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
    | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(X0,X1) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4472,c_2716])).

cnf(c_6052,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6051])).

cnf(c_6062,plain,
    ( v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(X0,sK2) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3006,c_6052])).

cnf(c_6215,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v2_compts_1(X0,sK2) != iProver_top
    | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6062,c_26])).

cnf(c_6216,plain,
    ( v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(X0,sK2) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_6215])).

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

cnf(c_452,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK3,sK2)
    | ~ v1_compts_1(k1_pre_topc(X1,X0))
    | ~ v1_compts_1(k1_pre_topc(sK2,sK3))
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_453,plain,
    ( ~ v2_compts_1(sK3,sK2)
    | ~ v1_compts_1(k1_pre_topc(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_472,plain,
    ( ~ v2_compts_1(k2_struct_0(X0),X0)
    | ~ v2_compts_1(sK3,sK2)
    | ~ l1_pre_topc(X0)
    | k1_pre_topc(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_453])).

cnf(c_473,plain,
    ( ~ v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3))
    | ~ v2_compts_1(sK3,sK2)
    | ~ l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_1578,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_474,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1774,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK2,sK3),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1775,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1774])).

cnf(c_1777,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1775])).

cnf(c_1816,plain,
    ( v2_compts_1(sK3,sK2) != iProver_top
    | v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1578,c_26,c_27,c_474,c_1777,c_1801])).

cnf(c_1817,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1816])).

cnf(c_2227,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2223,c_1817])).

cnf(c_6224,plain,
    ( v2_compts_1(sK3,sK2) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6216,c_2227])).

cnf(c_6568,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(sK1(X0,sK3),u1_struct_0(X0)) = iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3192,c_2035,c_6224])).

cnf(c_6577,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK1(k1_pre_topc(sK2,sK3),sK3),sK3) = iProver_top
    | r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2320,c_6568])).

cnf(c_6616,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK1(k1_pre_topc(sK2,sK3),sK3),sK3) = iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6577,c_2223])).

cnf(c_7146,plain,
    ( r1_tarski(sK1(k1_pre_topc(sK2,sK3),sK3),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6616,c_26,c_27,c_1801,c_2035])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1595,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7151,plain,
    ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
    | r1_tarski(sK3,sK1(k1_pre_topc(sK2,sK3),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7146,c_1595])).

cnf(c_15,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK1(X2,X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1584,plain,
    ( sK1(X0,X1) = X1
    | v2_compts_1(X1,X2) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | r1_tarski(X1,k2_struct_0(X0)) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3499,plain,
    ( sK1(X0,sK3) = sK3
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1581,c_1584])).

cnf(c_4158,plain,
    ( r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | sK1(X0,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3499,c_26])).

cnf(c_4159,plain,
    ( sK1(X0,sK3) = sK3
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4158])).

cnf(c_4168,plain,
    ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2223,c_4159])).

cnf(c_8154,plain,
    ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7151,c_26,c_27,c_1801,c_2035,c_4168,c_6224])).

cnf(c_14,plain,
    ( v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK1(X2,X0),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1585,plain,
    ( v2_compts_1(X0,X1) = iProver_top
    | v2_compts_1(sK1(X2,X0),X2) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3722,plain,
    ( v2_compts_1(sK1(X0,sK3),X0) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1581,c_1585])).

cnf(c_4028,plain,
    ( r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | v2_compts_1(sK1(X0,sK3),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3722,c_26])).

cnf(c_4029,plain,
    ( v2_compts_1(sK1(X0,sK3),X0) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4028])).

cnf(c_8161,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8154,c_4029])).

cnf(c_8179,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8161,c_2223])).

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

cnf(c_425,plain,
    ( v2_compts_1(X0,X1)
    | v2_compts_1(sK3,sK2)
    | v1_compts_1(k1_pre_topc(X1,X0))
    | v1_compts_1(k1_pre_topc(sK2,sK3))
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_426,plain,
    ( v2_compts_1(sK3,sK2)
    | v1_compts_1(k1_pre_topc(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_485,plain,
    ( v2_compts_1(k2_struct_0(X0),X0)
    | v2_compts_1(sK3,sK2)
    | ~ l1_pre_topc(X0)
    | k1_pre_topc(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_426])).

cnf(c_486,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3))
    | v2_compts_1(sK3,sK2)
    | ~ l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_1577,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_487,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_1829,plain,
    ( v2_compts_1(sK3,sK2) = iProver_top
    | v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1577,c_26,c_27,c_487,c_1777,c_1801])).

cnf(c_1830,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_1829])).

cnf(c_2226,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2223,c_1830])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8179,c_6224,c_2226,c_2035,c_1801,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:23:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.33/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/0.97  
% 3.33/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.33/0.97  
% 3.33/0.97  ------  iProver source info
% 3.33/0.97  
% 3.33/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.33/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.33/0.97  git: non_committed_changes: false
% 3.33/0.97  git: last_make_outside_of_git: false
% 3.33/0.97  
% 3.33/0.97  ------ 
% 3.33/0.97  
% 3.33/0.97  ------ Input Options
% 3.33/0.97  
% 3.33/0.97  --out_options                           all
% 3.33/0.97  --tptp_safe_out                         true
% 3.33/0.97  --problem_path                          ""
% 3.33/0.97  --include_path                          ""
% 3.33/0.97  --clausifier                            res/vclausify_rel
% 3.33/0.97  --clausifier_options                    --mode clausify
% 3.33/0.97  --stdin                                 false
% 3.33/0.97  --stats_out                             all
% 3.33/0.97  
% 3.33/0.97  ------ General Options
% 3.33/0.97  
% 3.33/0.97  --fof                                   false
% 3.33/0.97  --time_out_real                         305.
% 3.33/0.97  --time_out_virtual                      -1.
% 3.33/0.97  --symbol_type_check                     false
% 3.33/0.97  --clausify_out                          false
% 3.33/0.97  --sig_cnt_out                           false
% 3.33/0.97  --trig_cnt_out                          false
% 3.33/0.97  --trig_cnt_out_tolerance                1.
% 3.33/0.97  --trig_cnt_out_sk_spl                   false
% 3.33/0.97  --abstr_cl_out                          false
% 3.33/0.97  
% 3.33/0.97  ------ Global Options
% 3.33/0.97  
% 3.33/0.97  --schedule                              default
% 3.33/0.97  --add_important_lit                     false
% 3.33/0.97  --prop_solver_per_cl                    1000
% 3.33/0.97  --min_unsat_core                        false
% 3.33/0.97  --soft_assumptions                      false
% 3.33/0.97  --soft_lemma_size                       3
% 3.33/0.97  --prop_impl_unit_size                   0
% 3.33/0.97  --prop_impl_unit                        []
% 3.33/0.97  --share_sel_clauses                     true
% 3.33/0.97  --reset_solvers                         false
% 3.33/0.97  --bc_imp_inh                            [conj_cone]
% 3.33/0.97  --conj_cone_tolerance                   3.
% 3.33/0.97  --extra_neg_conj                        none
% 3.33/0.97  --large_theory_mode                     true
% 3.33/0.97  --prolific_symb_bound                   200
% 3.33/0.97  --lt_threshold                          2000
% 3.33/0.97  --clause_weak_htbl                      true
% 3.33/0.97  --gc_record_bc_elim                     false
% 3.33/0.97  
% 3.33/0.97  ------ Preprocessing Options
% 3.33/0.97  
% 3.33/0.97  --preprocessing_flag                    true
% 3.33/0.97  --time_out_prep_mult                    0.1
% 3.33/0.97  --splitting_mode                        input
% 3.33/0.97  --splitting_grd                         true
% 3.33/0.97  --splitting_cvd                         false
% 3.33/0.97  --splitting_cvd_svl                     false
% 3.33/0.97  --splitting_nvd                         32
% 3.33/0.97  --sub_typing                            true
% 3.33/0.97  --prep_gs_sim                           true
% 3.33/0.97  --prep_unflatten                        true
% 3.33/0.97  --prep_res_sim                          true
% 3.33/0.97  --prep_upred                            true
% 3.33/0.97  --prep_sem_filter                       exhaustive
% 3.33/0.97  --prep_sem_filter_out                   false
% 3.33/0.97  --pred_elim                             true
% 3.33/0.97  --res_sim_input                         true
% 3.33/0.97  --eq_ax_congr_red                       true
% 3.33/0.97  --pure_diseq_elim                       true
% 3.33/0.97  --brand_transform                       false
% 3.33/0.97  --non_eq_to_eq                          false
% 3.33/0.97  --prep_def_merge                        true
% 3.33/0.97  --prep_def_merge_prop_impl              false
% 3.33/0.97  --prep_def_merge_mbd                    true
% 3.33/0.97  --prep_def_merge_tr_red                 false
% 3.33/0.97  --prep_def_merge_tr_cl                  false
% 3.33/0.97  --smt_preprocessing                     true
% 3.33/0.97  --smt_ac_axioms                         fast
% 3.33/0.97  --preprocessed_out                      false
% 3.33/0.97  --preprocessed_stats                    false
% 3.33/0.97  
% 3.33/0.97  ------ Abstraction refinement Options
% 3.33/0.97  
% 3.33/0.97  --abstr_ref                             []
% 3.33/0.97  --abstr_ref_prep                        false
% 3.33/0.97  --abstr_ref_until_sat                   false
% 3.33/0.97  --abstr_ref_sig_restrict                funpre
% 3.33/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/0.97  --abstr_ref_under                       []
% 3.33/0.97  
% 3.33/0.97  ------ SAT Options
% 3.33/0.97  
% 3.33/0.97  --sat_mode                              false
% 3.33/0.97  --sat_fm_restart_options                ""
% 3.33/0.97  --sat_gr_def                            false
% 3.33/0.97  --sat_epr_types                         true
% 3.33/0.97  --sat_non_cyclic_types                  false
% 3.33/0.97  --sat_finite_models                     false
% 3.33/0.97  --sat_fm_lemmas                         false
% 3.33/0.97  --sat_fm_prep                           false
% 3.33/0.97  --sat_fm_uc_incr                        true
% 3.33/0.97  --sat_out_model                         small
% 3.33/0.97  --sat_out_clauses                       false
% 3.33/0.97  
% 3.33/0.97  ------ QBF Options
% 3.33/0.97  
% 3.33/0.97  --qbf_mode                              false
% 3.33/0.97  --qbf_elim_univ                         false
% 3.33/0.97  --qbf_dom_inst                          none
% 3.33/0.97  --qbf_dom_pre_inst                      false
% 3.33/0.97  --qbf_sk_in                             false
% 3.33/0.97  --qbf_pred_elim                         true
% 3.33/0.97  --qbf_split                             512
% 3.33/0.97  
% 3.33/0.97  ------ BMC1 Options
% 3.33/0.97  
% 3.33/0.97  --bmc1_incremental                      false
% 3.33/0.97  --bmc1_axioms                           reachable_all
% 3.33/0.97  --bmc1_min_bound                        0
% 3.33/0.97  --bmc1_max_bound                        -1
% 3.33/0.97  --bmc1_max_bound_default                -1
% 3.33/0.97  --bmc1_symbol_reachability              true
% 3.33/0.97  --bmc1_property_lemmas                  false
% 3.33/0.97  --bmc1_k_induction                      false
% 3.33/0.97  --bmc1_non_equiv_states                 false
% 3.33/0.97  --bmc1_deadlock                         false
% 3.33/0.97  --bmc1_ucm                              false
% 3.33/0.97  --bmc1_add_unsat_core                   none
% 3.33/0.97  --bmc1_unsat_core_children              false
% 3.33/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/0.97  --bmc1_out_stat                         full
% 3.33/0.97  --bmc1_ground_init                      false
% 3.33/0.97  --bmc1_pre_inst_next_state              false
% 3.33/0.97  --bmc1_pre_inst_state                   false
% 3.33/0.97  --bmc1_pre_inst_reach_state             false
% 3.33/0.97  --bmc1_out_unsat_core                   false
% 3.33/0.97  --bmc1_aig_witness_out                  false
% 3.33/0.97  --bmc1_verbose                          false
% 3.33/0.97  --bmc1_dump_clauses_tptp                false
% 3.33/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.33/0.97  --bmc1_dump_file                        -
% 3.33/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.33/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.33/0.97  --bmc1_ucm_extend_mode                  1
% 3.33/0.97  --bmc1_ucm_init_mode                    2
% 3.33/0.97  --bmc1_ucm_cone_mode                    none
% 3.33/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.33/0.97  --bmc1_ucm_relax_model                  4
% 3.33/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.33/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/0.97  --bmc1_ucm_layered_model                none
% 3.33/0.97  --bmc1_ucm_max_lemma_size               10
% 3.33/0.97  
% 3.33/0.97  ------ AIG Options
% 3.33/0.97  
% 3.33/0.97  --aig_mode                              false
% 3.33/0.97  
% 3.33/0.97  ------ Instantiation Options
% 3.33/0.97  
% 3.33/0.97  --instantiation_flag                    true
% 3.33/0.97  --inst_sos_flag                         false
% 3.33/0.97  --inst_sos_phase                        true
% 3.33/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/0.97  --inst_lit_sel_side                     num_symb
% 3.33/0.97  --inst_solver_per_active                1400
% 3.33/0.97  --inst_solver_calls_frac                1.
% 3.33/0.97  --inst_passive_queue_type               priority_queues
% 3.33/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/0.97  --inst_passive_queues_freq              [25;2]
% 3.33/0.97  --inst_dismatching                      true
% 3.33/0.97  --inst_eager_unprocessed_to_passive     true
% 3.33/0.97  --inst_prop_sim_given                   true
% 3.33/0.97  --inst_prop_sim_new                     false
% 3.33/0.97  --inst_subs_new                         false
% 3.33/0.97  --inst_eq_res_simp                      false
% 3.33/0.97  --inst_subs_given                       false
% 3.33/0.97  --inst_orphan_elimination               true
% 3.33/0.97  --inst_learning_loop_flag               true
% 3.33/0.97  --inst_learning_start                   3000
% 3.33/0.97  --inst_learning_factor                  2
% 3.33/0.97  --inst_start_prop_sim_after_learn       3
% 3.33/0.97  --inst_sel_renew                        solver
% 3.33/0.97  --inst_lit_activity_flag                true
% 3.33/0.97  --inst_restr_to_given                   false
% 3.33/0.97  --inst_activity_threshold               500
% 3.33/0.97  --inst_out_proof                        true
% 3.33/0.97  
% 3.33/0.97  ------ Resolution Options
% 3.33/0.97  
% 3.33/0.97  --resolution_flag                       true
% 3.33/0.97  --res_lit_sel                           adaptive
% 3.33/0.97  --res_lit_sel_side                      none
% 3.33/0.97  --res_ordering                          kbo
% 3.33/0.97  --res_to_prop_solver                    active
% 3.33/0.97  --res_prop_simpl_new                    false
% 3.33/0.97  --res_prop_simpl_given                  true
% 3.33/0.97  --res_passive_queue_type                priority_queues
% 3.33/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/0.97  --res_passive_queues_freq               [15;5]
% 3.33/0.97  --res_forward_subs                      full
% 3.33/0.97  --res_backward_subs                     full
% 3.33/0.97  --res_forward_subs_resolution           true
% 3.33/0.97  --res_backward_subs_resolution          true
% 3.33/0.97  --res_orphan_elimination                true
% 3.33/0.97  --res_time_limit                        2.
% 3.33/0.97  --res_out_proof                         true
% 3.33/0.97  
% 3.33/0.97  ------ Superposition Options
% 3.33/0.97  
% 3.33/0.97  --superposition_flag                    true
% 3.33/0.97  --sup_passive_queue_type                priority_queues
% 3.33/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.33/0.97  --demod_completeness_check              fast
% 3.33/0.97  --demod_use_ground                      true
% 3.33/0.97  --sup_to_prop_solver                    passive
% 3.33/0.97  --sup_prop_simpl_new                    true
% 3.33/0.97  --sup_prop_simpl_given                  true
% 3.33/0.97  --sup_fun_splitting                     false
% 3.33/0.97  --sup_smt_interval                      50000
% 3.33/0.97  
% 3.33/0.97  ------ Superposition Simplification Setup
% 3.33/0.97  
% 3.33/0.97  --sup_indices_passive                   []
% 3.33/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.97  --sup_full_bw                           [BwDemod]
% 3.33/0.97  --sup_immed_triv                        [TrivRules]
% 3.33/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.97  --sup_immed_bw_main                     []
% 3.33/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.97  
% 3.33/0.97  ------ Combination Options
% 3.33/0.97  
% 3.33/0.97  --comb_res_mult                         3
% 3.33/0.97  --comb_sup_mult                         2
% 3.33/0.97  --comb_inst_mult                        10
% 3.33/0.97  
% 3.33/0.97  ------ Debug Options
% 3.33/0.97  
% 3.33/0.97  --dbg_backtrace                         false
% 3.33/0.97  --dbg_dump_prop_clauses                 false
% 3.33/0.97  --dbg_dump_prop_clauses_file            -
% 3.33/0.97  --dbg_out_stat                          false
% 3.33/0.97  ------ Parsing...
% 3.33/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.33/0.97  
% 3.33/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.33/0.97  
% 3.33/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.33/0.97  
% 3.33/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.33/0.97  ------ Proving...
% 3.33/0.97  ------ Problem Properties 
% 3.33/0.97  
% 3.33/0.97  
% 3.33/0.97  clauses                                 20
% 3.33/0.97  conjectures                             2
% 3.33/0.97  EPR                                     5
% 3.33/0.97  Horn                                    17
% 3.33/0.97  unary                                   3
% 3.33/0.97  binary                                  3
% 3.33/0.97  lits                                    67
% 3.33/0.97  lits eq                                 7
% 3.33/0.97  fd_pure                                 0
% 3.33/0.97  fd_pseudo                               0
% 3.33/0.97  fd_cond                                 0
% 3.33/0.97  fd_pseudo_cond                          1
% 3.33/0.97  AC symbols                              0
% 3.33/0.97  
% 3.33/0.97  ------ Schedule dynamic 5 is on 
% 3.33/0.97  
% 3.33/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.33/0.97  
% 3.33/0.97  
% 3.33/0.97  ------ 
% 3.33/0.97  Current options:
% 3.33/0.97  ------ 
% 3.33/0.97  
% 3.33/0.97  ------ Input Options
% 3.33/0.97  
% 3.33/0.97  --out_options                           all
% 3.33/0.97  --tptp_safe_out                         true
% 3.33/0.97  --problem_path                          ""
% 3.33/0.97  --include_path                          ""
% 3.33/0.97  --clausifier                            res/vclausify_rel
% 3.33/0.97  --clausifier_options                    --mode clausify
% 3.33/0.97  --stdin                                 false
% 3.33/0.97  --stats_out                             all
% 3.33/0.97  
% 3.33/0.97  ------ General Options
% 3.33/0.97  
% 3.33/0.97  --fof                                   false
% 3.33/0.97  --time_out_real                         305.
% 3.33/0.97  --time_out_virtual                      -1.
% 3.33/0.97  --symbol_type_check                     false
% 3.33/0.97  --clausify_out                          false
% 3.33/0.97  --sig_cnt_out                           false
% 3.33/0.97  --trig_cnt_out                          false
% 3.33/0.97  --trig_cnt_out_tolerance                1.
% 3.33/0.97  --trig_cnt_out_sk_spl                   false
% 3.33/0.97  --abstr_cl_out                          false
% 3.33/0.97  
% 3.33/0.97  ------ Global Options
% 3.33/0.97  
% 3.33/0.97  --schedule                              default
% 3.33/0.97  --add_important_lit                     false
% 3.33/0.97  --prop_solver_per_cl                    1000
% 3.33/0.97  --min_unsat_core                        false
% 3.33/0.97  --soft_assumptions                      false
% 3.33/0.97  --soft_lemma_size                       3
% 3.33/0.97  --prop_impl_unit_size                   0
% 3.33/0.97  --prop_impl_unit                        []
% 3.33/0.97  --share_sel_clauses                     true
% 3.33/0.97  --reset_solvers                         false
% 3.33/0.97  --bc_imp_inh                            [conj_cone]
% 3.33/0.97  --conj_cone_tolerance                   3.
% 3.33/0.97  --extra_neg_conj                        none
% 3.33/0.97  --large_theory_mode                     true
% 3.33/0.97  --prolific_symb_bound                   200
% 3.33/0.97  --lt_threshold                          2000
% 3.33/0.97  --clause_weak_htbl                      true
% 3.33/0.97  --gc_record_bc_elim                     false
% 3.33/0.97  
% 3.33/0.97  ------ Preprocessing Options
% 3.33/0.97  
% 3.33/0.97  --preprocessing_flag                    true
% 3.33/0.97  --time_out_prep_mult                    0.1
% 3.33/0.97  --splitting_mode                        input
% 3.33/0.97  --splitting_grd                         true
% 3.33/0.97  --splitting_cvd                         false
% 3.33/0.97  --splitting_cvd_svl                     false
% 3.33/0.97  --splitting_nvd                         32
% 3.33/0.97  --sub_typing                            true
% 3.33/0.97  --prep_gs_sim                           true
% 3.33/0.97  --prep_unflatten                        true
% 3.33/0.97  --prep_res_sim                          true
% 3.33/0.97  --prep_upred                            true
% 3.33/0.97  --prep_sem_filter                       exhaustive
% 3.33/0.97  --prep_sem_filter_out                   false
% 3.33/0.97  --pred_elim                             true
% 3.33/0.97  --res_sim_input                         true
% 3.33/0.97  --eq_ax_congr_red                       true
% 3.33/0.97  --pure_diseq_elim                       true
% 3.33/0.97  --brand_transform                       false
% 3.33/0.97  --non_eq_to_eq                          false
% 3.33/0.97  --prep_def_merge                        true
% 3.33/0.97  --prep_def_merge_prop_impl              false
% 3.33/0.97  --prep_def_merge_mbd                    true
% 3.33/0.97  --prep_def_merge_tr_red                 false
% 3.33/0.97  --prep_def_merge_tr_cl                  false
% 3.33/0.97  --smt_preprocessing                     true
% 3.33/0.97  --smt_ac_axioms                         fast
% 3.33/0.97  --preprocessed_out                      false
% 3.33/0.97  --preprocessed_stats                    false
% 3.33/0.97  
% 3.33/0.97  ------ Abstraction refinement Options
% 3.33/0.97  
% 3.33/0.97  --abstr_ref                             []
% 3.33/0.97  --abstr_ref_prep                        false
% 3.33/0.97  --abstr_ref_until_sat                   false
% 3.33/0.97  --abstr_ref_sig_restrict                funpre
% 3.33/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/0.97  --abstr_ref_under                       []
% 3.33/0.97  
% 3.33/0.97  ------ SAT Options
% 3.33/0.97  
% 3.33/0.97  --sat_mode                              false
% 3.33/0.97  --sat_fm_restart_options                ""
% 3.33/0.97  --sat_gr_def                            false
% 3.33/0.97  --sat_epr_types                         true
% 3.33/0.97  --sat_non_cyclic_types                  false
% 3.33/0.97  --sat_finite_models                     false
% 3.33/0.97  --sat_fm_lemmas                         false
% 3.33/0.97  --sat_fm_prep                           false
% 3.33/0.97  --sat_fm_uc_incr                        true
% 3.33/0.97  --sat_out_model                         small
% 3.33/0.97  --sat_out_clauses                       false
% 3.33/0.97  
% 3.33/0.97  ------ QBF Options
% 3.33/0.97  
% 3.33/0.97  --qbf_mode                              false
% 3.33/0.97  --qbf_elim_univ                         false
% 3.33/0.97  --qbf_dom_inst                          none
% 3.33/0.97  --qbf_dom_pre_inst                      false
% 3.33/0.97  --qbf_sk_in                             false
% 3.33/0.97  --qbf_pred_elim                         true
% 3.33/0.97  --qbf_split                             512
% 3.33/0.97  
% 3.33/0.97  ------ BMC1 Options
% 3.33/0.97  
% 3.33/0.97  --bmc1_incremental                      false
% 3.33/0.97  --bmc1_axioms                           reachable_all
% 3.33/0.97  --bmc1_min_bound                        0
% 3.33/0.97  --bmc1_max_bound                        -1
% 3.33/0.97  --bmc1_max_bound_default                -1
% 3.33/0.97  --bmc1_symbol_reachability              true
% 3.33/0.97  --bmc1_property_lemmas                  false
% 3.33/0.97  --bmc1_k_induction                      false
% 3.33/0.97  --bmc1_non_equiv_states                 false
% 3.33/0.97  --bmc1_deadlock                         false
% 3.33/0.97  --bmc1_ucm                              false
% 3.33/0.97  --bmc1_add_unsat_core                   none
% 3.33/0.97  --bmc1_unsat_core_children              false
% 3.33/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/0.97  --bmc1_out_stat                         full
% 3.33/0.97  --bmc1_ground_init                      false
% 3.33/0.97  --bmc1_pre_inst_next_state              false
% 3.33/0.97  --bmc1_pre_inst_state                   false
% 3.33/0.97  --bmc1_pre_inst_reach_state             false
% 3.33/0.97  --bmc1_out_unsat_core                   false
% 3.33/0.97  --bmc1_aig_witness_out                  false
% 3.33/0.97  --bmc1_verbose                          false
% 3.33/0.97  --bmc1_dump_clauses_tptp                false
% 3.33/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.33/0.97  --bmc1_dump_file                        -
% 3.33/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.33/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.33/0.97  --bmc1_ucm_extend_mode                  1
% 3.33/0.97  --bmc1_ucm_init_mode                    2
% 3.33/0.97  --bmc1_ucm_cone_mode                    none
% 3.33/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.33/0.97  --bmc1_ucm_relax_model                  4
% 3.33/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.33/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/0.97  --bmc1_ucm_layered_model                none
% 3.33/0.97  --bmc1_ucm_max_lemma_size               10
% 3.33/0.97  
% 3.33/0.97  ------ AIG Options
% 3.33/0.97  
% 3.33/0.97  --aig_mode                              false
% 3.33/0.97  
% 3.33/0.97  ------ Instantiation Options
% 3.33/0.97  
% 3.33/0.97  --instantiation_flag                    true
% 3.33/0.97  --inst_sos_flag                         false
% 3.33/0.97  --inst_sos_phase                        true
% 3.33/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/0.97  --inst_lit_sel_side                     none
% 3.33/0.97  --inst_solver_per_active                1400
% 3.33/0.97  --inst_solver_calls_frac                1.
% 3.33/0.97  --inst_passive_queue_type               priority_queues
% 3.33/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/0.97  --inst_passive_queues_freq              [25;2]
% 3.33/0.97  --inst_dismatching                      true
% 3.33/0.97  --inst_eager_unprocessed_to_passive     true
% 3.33/0.97  --inst_prop_sim_given                   true
% 3.33/0.97  --inst_prop_sim_new                     false
% 3.33/0.97  --inst_subs_new                         false
% 3.33/0.97  --inst_eq_res_simp                      false
% 3.33/0.97  --inst_subs_given                       false
% 3.33/0.97  --inst_orphan_elimination               true
% 3.33/0.97  --inst_learning_loop_flag               true
% 3.33/0.97  --inst_learning_start                   3000
% 3.33/0.97  --inst_learning_factor                  2
% 3.33/0.97  --inst_start_prop_sim_after_learn       3
% 3.33/0.97  --inst_sel_renew                        solver
% 3.33/0.97  --inst_lit_activity_flag                true
% 3.33/0.97  --inst_restr_to_given                   false
% 3.33/0.97  --inst_activity_threshold               500
% 3.33/0.97  --inst_out_proof                        true
% 3.33/0.97  
% 3.33/0.97  ------ Resolution Options
% 3.33/0.97  
% 3.33/0.97  --resolution_flag                       false
% 3.33/0.97  --res_lit_sel                           adaptive
% 3.33/0.97  --res_lit_sel_side                      none
% 3.33/0.97  --res_ordering                          kbo
% 3.33/0.97  --res_to_prop_solver                    active
% 3.33/0.97  --res_prop_simpl_new                    false
% 3.33/0.97  --res_prop_simpl_given                  true
% 3.33/0.97  --res_passive_queue_type                priority_queues
% 3.33/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/0.97  --res_passive_queues_freq               [15;5]
% 3.33/0.97  --res_forward_subs                      full
% 3.33/0.97  --res_backward_subs                     full
% 3.33/0.97  --res_forward_subs_resolution           true
% 3.33/0.97  --res_backward_subs_resolution          true
% 3.33/0.97  --res_orphan_elimination                true
% 3.33/0.97  --res_time_limit                        2.
% 3.33/0.97  --res_out_proof                         true
% 3.33/0.97  
% 3.33/0.97  ------ Superposition Options
% 3.33/0.97  
% 3.33/0.97  --superposition_flag                    true
% 3.33/0.97  --sup_passive_queue_type                priority_queues
% 3.33/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.33/0.97  --demod_completeness_check              fast
% 3.33/0.97  --demod_use_ground                      true
% 3.33/0.97  --sup_to_prop_solver                    passive
% 3.33/0.97  --sup_prop_simpl_new                    true
% 3.33/0.97  --sup_prop_simpl_given                  true
% 3.33/0.97  --sup_fun_splitting                     false
% 3.33/0.97  --sup_smt_interval                      50000
% 3.33/0.97  
% 3.33/0.97  ------ Superposition Simplification Setup
% 3.33/0.97  
% 3.33/0.97  --sup_indices_passive                   []
% 3.33/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.97  --sup_full_bw                           [BwDemod]
% 3.33/0.97  --sup_immed_triv                        [TrivRules]
% 3.33/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.97  --sup_immed_bw_main                     []
% 3.33/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.97  
% 3.33/0.97  ------ Combination Options
% 3.33/0.97  
% 3.33/0.97  --comb_res_mult                         3
% 3.33/0.97  --comb_sup_mult                         2
% 3.33/0.97  --comb_inst_mult                        10
% 3.33/0.97  
% 3.33/0.97  ------ Debug Options
% 3.33/0.97  
% 3.33/0.97  --dbg_backtrace                         false
% 3.33/0.97  --dbg_dump_prop_clauses                 false
% 3.33/0.97  --dbg_dump_prop_clauses_file            -
% 3.33/0.97  --dbg_out_stat                          false
% 3.33/0.97  
% 3.33/0.97  
% 3.33/0.97  
% 3.33/0.97  
% 3.33/0.97  ------ Proving...
% 3.33/0.97  
% 3.33/0.97  
% 3.33/0.97  % SZS status Theorem for theBenchmark.p
% 3.33/0.97  
% 3.33/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.33/0.97  
% 3.33/0.97  fof(f10,conjecture,(
% 3.33/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 3.33/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.97  
% 3.33/0.97  fof(f11,negated_conjecture,(
% 3.33/0.97    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 3.33/0.97    inference(negated_conjecture,[],[f10])).
% 3.33/0.97  
% 3.33/0.97  fof(f12,plain,(
% 3.33/0.97    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 3.33/0.97    inference(pure_predicate_removal,[],[f11])).
% 3.33/0.97  
% 3.33/0.97  fof(f23,plain,(
% 3.33/0.97    ? [X0] : (? [X1] : ((((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 != X1) | ((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.33/0.97    inference(ennf_transformation,[],[f12])).
% 3.33/0.97  
% 3.33/0.97  fof(f24,plain,(
% 3.33/0.97    ! [X1,X0] : (((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 = X1) | ~sP0(X1,X0))),
% 3.33/0.97    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.33/0.97  
% 3.33/0.97  fof(f25,plain,(
% 3.33/0.97    ? [X0] : (? [X1] : ((((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.33/0.97    inference(definition_folding,[],[f23,f24])).
% 3.33/0.97  
% 3.33/0.97  fof(f38,plain,(
% 3.33/0.97    ? [X0] : (? [X1] : (((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0))) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.33/0.97    inference(nnf_transformation,[],[f25])).
% 3.33/0.97  
% 3.33/0.97  fof(f39,plain,(
% 3.33/0.97    ? [X0] : (? [X1] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.33/0.97    inference(flattening,[],[f38])).
% 3.33/0.97  
% 3.33/0.97  fof(f41,plain,(
% 3.33/0.97    ( ! [X0] : (? [X1] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((((~v1_compts_1(k1_pre_topc(X0,sK3)) | ~v2_compts_1(sK3,X0)) & (v1_compts_1(k1_pre_topc(X0,sK3)) | v2_compts_1(sK3,X0)) & k1_xboole_0 != sK3) | sP0(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.33/0.97    introduced(choice_axiom,[])).
% 3.33/0.97  
% 3.33/0.97  fof(f40,plain,(
% 3.33/0.97    ? [X0] : (? [X1] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((((~v1_compts_1(k1_pre_topc(sK2,X1)) | ~v2_compts_1(X1,sK2)) & (v1_compts_1(k1_pre_topc(sK2,X1)) | v2_compts_1(X1,sK2)) & k1_xboole_0 != X1) | sP0(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 3.33/0.97    introduced(choice_axiom,[])).
% 3.33/0.97  
% 3.33/0.97  fof(f42,plain,(
% 3.33/0.97    ((((~v1_compts_1(k1_pre_topc(sK2,sK3)) | ~v2_compts_1(sK3,sK2)) & (v1_compts_1(k1_pre_topc(sK2,sK3)) | v2_compts_1(sK3,sK2)) & k1_xboole_0 != sK3) | sP0(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 3.33/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f41,f40])).
% 3.33/0.97  
% 3.33/0.97  fof(f65,plain,(
% 3.33/0.97    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.33/0.97    inference(cnf_transformation,[],[f42])).
% 3.33/0.97  
% 3.33/0.97  fof(f6,axiom,(
% 3.33/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 3.33/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.97  
% 3.33/0.97  fof(f18,plain,(
% 3.33/0.97    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.33/0.97    inference(ennf_transformation,[],[f6])).
% 3.33/0.97  
% 3.33/0.97  fof(f53,plain,(
% 3.33/0.97    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.33/0.97    inference(cnf_transformation,[],[f18])).
% 3.33/0.97  
% 3.33/0.97  fof(f64,plain,(
% 3.33/0.97    l1_pre_topc(sK2)),
% 3.33/0.97    inference(cnf_transformation,[],[f42])).
% 3.33/0.97  
% 3.33/0.97  fof(f9,axiom,(
% 3.33/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 3.33/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.97  
% 3.33/0.97  fof(f21,plain,(
% 3.33/0.97    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.33/0.97    inference(ennf_transformation,[],[f9])).
% 3.33/0.97  
% 3.33/0.97  fof(f22,plain,(
% 3.33/0.97    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.33/0.97    inference(flattening,[],[f21])).
% 3.33/0.97  
% 3.33/0.97  fof(f31,plain,(
% 3.33/0.97    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.33/0.97    inference(nnf_transformation,[],[f22])).
% 3.33/0.97  
% 3.33/0.97  fof(f32,plain,(
% 3.33/0.97    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.33/0.97    inference(rectify,[],[f31])).
% 3.33/0.97  
% 3.33/0.97  fof(f33,plain,(
% 3.33/0.97    ! [X2,X1] : (? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v2_compts_1(sK1(X1,X2),X1) & sK1(X1,X2) = X2 & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 3.33/0.97    introduced(choice_axiom,[])).
% 3.33/0.97  
% 3.33/0.97  fof(f34,plain,(
% 3.33/0.97    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | (~v2_compts_1(sK1(X1,X2),X1) & sK1(X1,X2) = X2 & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.33/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 3.33/0.97  
% 3.33/0.97  fof(f58,plain,(
% 3.33/0.97    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.33/0.97    inference(cnf_transformation,[],[f34])).
% 3.33/0.97  
% 3.33/0.97  fof(f2,axiom,(
% 3.33/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.33/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.97  
% 3.33/0.97  fof(f28,plain,(
% 3.33/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.33/0.97    inference(nnf_transformation,[],[f2])).
% 3.33/0.97  
% 3.33/0.97  fof(f46,plain,(
% 3.33/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.33/0.97    inference(cnf_transformation,[],[f28])).
% 3.33/0.97  
% 3.33/0.97  fof(f1,axiom,(
% 3.33/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.33/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.97  
% 3.33/0.97  fof(f26,plain,(
% 3.33/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.33/0.97    inference(nnf_transformation,[],[f1])).
% 3.33/0.97  
% 3.33/0.97  fof(f27,plain,(
% 3.33/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.33/0.97    inference(flattening,[],[f26])).
% 3.33/0.97  
% 3.33/0.97  fof(f43,plain,(
% 3.33/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.33/0.97    inference(cnf_transformation,[],[f27])).
% 3.33/0.97  
% 3.33/0.97  fof(f70,plain,(
% 3.33/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.33/0.97    inference(equality_resolution,[],[f43])).
% 3.33/0.97  
% 3.33/0.97  fof(f4,axiom,(
% 3.33/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 3.33/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.97  
% 3.33/0.97  fof(f15,plain,(
% 3.33/0.97    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.33/0.97    inference(ennf_transformation,[],[f4])).
% 3.33/0.97  
% 3.33/0.97  fof(f16,plain,(
% 3.33/0.97    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.33/0.97    inference(flattening,[],[f15])).
% 3.33/0.97  
% 3.33/0.97  fof(f51,plain,(
% 3.33/0.97    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.33/0.97    inference(cnf_transformation,[],[f16])).
% 3.33/0.97  
% 3.33/0.97  fof(f57,plain,(
% 3.33/0.97    ( ! [X4,X2,X0,X1] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.33/0.97    inference(cnf_transformation,[],[f34])).
% 3.33/0.97  
% 3.33/0.97  fof(f73,plain,(
% 3.33/0.97    ( ! [X4,X0,X1] : (v2_compts_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X4,X0) | ~r1_tarski(X4,k2_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.33/0.97    inference(equality_resolution,[],[f57])).
% 3.33/0.97  
% 3.33/0.97  fof(f7,axiom,(
% 3.33/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.33/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.97  
% 3.33/0.97  fof(f19,plain,(
% 3.33/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.33/0.97    inference(ennf_transformation,[],[f7])).
% 3.33/0.97  
% 3.33/0.97  fof(f54,plain,(
% 3.33/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.33/0.97    inference(cnf_transformation,[],[f19])).
% 3.33/0.97  
% 3.33/0.97  fof(f3,axiom,(
% 3.33/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 3.33/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.97  
% 3.33/0.97  fof(f13,plain,(
% 3.33/0.97    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.33/0.97    inference(ennf_transformation,[],[f3])).
% 3.33/0.97  
% 3.33/0.97  fof(f14,plain,(
% 3.33/0.97    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.33/0.97    inference(flattening,[],[f13])).
% 3.33/0.97  
% 3.33/0.97  fof(f29,plain,(
% 3.33/0.97    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.33/0.97    inference(nnf_transformation,[],[f14])).
% 3.33/0.97  
% 3.33/0.97  fof(f48,plain,(
% 3.33/0.97    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.33/0.97    inference(cnf_transformation,[],[f29])).
% 3.33/0.97  
% 3.33/0.97  fof(f72,plain,(
% 3.33/0.97    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.33/0.97    inference(equality_resolution,[],[f48])).
% 3.33/0.97  
% 3.33/0.97  fof(f50,plain,(
% 3.33/0.97    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.33/0.97    inference(cnf_transformation,[],[f16])).
% 3.33/0.97  
% 3.33/0.97  fof(f47,plain,(
% 3.33/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.33/0.97    inference(cnf_transformation,[],[f28])).
% 3.33/0.97  
% 3.33/0.97  fof(f8,axiom,(
% 3.33/0.97    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 3.33/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.97  
% 3.33/0.97  fof(f20,plain,(
% 3.33/0.97    ! [X0] : ((v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)) | ~l1_pre_topc(X0))),
% 3.33/0.97    inference(ennf_transformation,[],[f8])).
% 3.33/0.97  
% 3.33/0.97  fof(f30,plain,(
% 3.33/0.97    ! [X0] : (((v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0)) & (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 3.33/0.97    inference(nnf_transformation,[],[f20])).
% 3.33/0.97  
% 3.33/0.97  fof(f56,plain,(
% 3.33/0.97    ( ! [X0] : (v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0)) )),
% 3.33/0.97    inference(cnf_transformation,[],[f30])).
% 3.33/0.97  
% 3.33/0.97  fof(f35,plain,(
% 3.33/0.97    ! [X1,X0] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0))) & k1_xboole_0 = X1) | ~sP0(X1,X0))),
% 3.33/0.97    inference(nnf_transformation,[],[f24])).
% 3.33/0.97  
% 3.33/0.97  fof(f36,plain,(
% 3.33/0.97    ! [X1,X0] : (((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 = X1) | ~sP0(X1,X0))),
% 3.33/0.97    inference(flattening,[],[f35])).
% 3.33/0.97  
% 3.33/0.97  fof(f37,plain,(
% 3.33/0.97    ! [X0,X1] : (((~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1)) & (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1)) & k1_xboole_0 = X0) | ~sP0(X0,X1))),
% 3.33/0.97    inference(rectify,[],[f36])).
% 3.33/0.97  
% 3.33/0.97  fof(f63,plain,(
% 3.33/0.97    ( ! [X0,X1] : (~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1) | ~sP0(X0,X1)) )),
% 3.33/0.97    inference(cnf_transformation,[],[f37])).
% 3.33/0.97  
% 3.33/0.97  fof(f68,plain,(
% 3.33/0.97    ~v1_compts_1(k1_pre_topc(sK2,sK3)) | ~v2_compts_1(sK3,sK2) | sP0(sK3,sK2)),
% 3.33/0.97    inference(cnf_transformation,[],[f42])).
% 3.33/0.98  
% 3.33/0.98  fof(f5,axiom,(
% 3.33/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.33/0.98  
% 3.33/0.98  fof(f17,plain,(
% 3.33/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.33/0.98    inference(ennf_transformation,[],[f5])).
% 3.33/0.98  
% 3.33/0.98  fof(f52,plain,(
% 3.33/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f17])).
% 3.33/0.98  
% 3.33/0.98  fof(f45,plain,(
% 3.33/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f27])).
% 3.33/0.98  
% 3.33/0.98  fof(f59,plain,(
% 3.33/0.98    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | sK1(X1,X2) = X2 | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f34])).
% 3.33/0.98  
% 3.33/0.98  fof(f60,plain,(
% 3.33/0.98    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(sK1(X1,X2),X1) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f34])).
% 3.33/0.98  
% 3.33/0.98  fof(f55,plain,(
% 3.33/0.98    ( ! [X0] : (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f30])).
% 3.33/0.98  
% 3.33/0.98  fof(f62,plain,(
% 3.33/0.98    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1) | ~sP0(X0,X1)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f37])).
% 3.33/0.98  
% 3.33/0.98  fof(f67,plain,(
% 3.33/0.98    v1_compts_1(k1_pre_topc(sK2,sK3)) | v2_compts_1(sK3,sK2) | sP0(sK3,sK2)),
% 3.33/0.98    inference(cnf_transformation,[],[f42])).
% 3.33/0.98  
% 3.33/0.98  cnf(c_24,negated_conjecture,
% 3.33/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.33/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1581,plain,
% 3.33/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_10,plain,
% 3.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.98      | ~ l1_pre_topc(X1)
% 3.33/0.98      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 3.33/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1587,plain,
% 3.33/0.98      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
% 3.33/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.33/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_2068,plain,
% 3.33/0.98      ( u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3
% 3.33/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_1581,c_1587]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_25,negated_conjecture,
% 3.33/0.98      ( l1_pre_topc(sK2) ),
% 3.33/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1804,plain,
% 3.33/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.33/0.98      | ~ l1_pre_topc(sK2)
% 3.33/0.98      | u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_2320,plain,
% 3.33/0.98      ( u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
% 3.33/0.98      inference(global_propositional_subsumption,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_2068,c_25,c_24,c_1804]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_16,plain,
% 3.33/0.98      ( v2_compts_1(X0,X1)
% 3.33/0.98      | ~ m1_pre_topc(X2,X1)
% 3.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.98      | m1_subset_1(sK1(X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 3.33/0.98      | ~ r1_tarski(X0,k2_struct_0(X2))
% 3.33/0.98      | ~ l1_pre_topc(X1) ),
% 3.33/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1583,plain,
% 3.33/0.98      ( v2_compts_1(X0,X1) = iProver_top
% 3.33/0.98      | m1_pre_topc(X2,X1) != iProver_top
% 3.33/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.33/0.98      | m1_subset_1(sK1(X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 3.33/0.98      | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
% 3.33/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_2604,plain,
% 3.33/0.98      ( v2_compts_1(sK3,sK2) = iProver_top
% 3.33/0.98      | m1_pre_topc(X0,sK2) != iProver_top
% 3.33/0.98      | m1_subset_1(sK1(X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.33/0.98      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
% 3.33/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_1581,c_1583]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_26,plain,
% 3.33/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3181,plain,
% 3.33/0.98      ( r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
% 3.33/0.98      | m1_subset_1(sK1(X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.33/0.98      | m1_pre_topc(X0,sK2) != iProver_top
% 3.33/0.98      | v2_compts_1(sK3,sK2) = iProver_top ),
% 3.33/0.98      inference(global_propositional_subsumption,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_2604,c_26]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3182,plain,
% 3.33/0.98      ( v2_compts_1(sK3,sK2) = iProver_top
% 3.33/0.98      | m1_pre_topc(X0,sK2) != iProver_top
% 3.33/0.98      | m1_subset_1(sK1(X0,sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.33/0.98      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
% 3.33/0.98      inference(renaming,[status(thm)],[c_3181]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_4,plain,
% 3.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.33/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1592,plain,
% 3.33/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.33/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3192,plain,
% 3.33/0.98      ( v2_compts_1(sK3,sK2) = iProver_top
% 3.33/0.98      | m1_pre_topc(X0,sK2) != iProver_top
% 3.33/0.98      | r1_tarski(sK1(X0,sK3),u1_struct_0(X0)) = iProver_top
% 3.33/0.98      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_3182,c_1592]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_2,plain,
% 3.33/0.98      ( r1_tarski(X0,X0) ),
% 3.33/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_2032,plain,
% 3.33/0.98      ( r1_tarski(sK3,sK3) ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_2035,plain,
% 3.33/0.98      ( r1_tarski(sK3,sK3) = iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_2032]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_7,plain,
% 3.33/0.98      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 3.33/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.33/0.98      | ~ l1_pre_topc(X0) ),
% 3.33/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1590,plain,
% 3.33/0.98      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 3.33/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.33/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_2741,plain,
% 3.33/0.98      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top
% 3.33/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_1581,c_1590]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_27,plain,
% 3.33/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1800,plain,
% 3.33/0.98      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
% 3.33/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.33/0.98      | ~ l1_pre_topc(sK2) ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1801,plain,
% 3.33/0.98      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top
% 3.33/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.33/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_1800]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3006,plain,
% 3.33/0.98      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top ),
% 3.33/0.98      inference(global_propositional_subsumption,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_2741,c_26,c_27,c_1801]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_17,plain,
% 3.33/0.98      ( ~ v2_compts_1(X0,X1)
% 3.33/0.98      | v2_compts_1(X0,X2)
% 3.33/0.98      | ~ m1_pre_topc(X2,X1)
% 3.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.98      | ~ r1_tarski(X0,k2_struct_0(X2))
% 3.33/0.98      | ~ l1_pre_topc(X1) ),
% 3.33/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1582,plain,
% 3.33/0.98      ( v2_compts_1(X0,X1) != iProver_top
% 3.33/0.98      | v2_compts_1(X0,X2) = iProver_top
% 3.33/0.98      | m1_pre_topc(X2,X1) != iProver_top
% 3.33/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 3.33/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.33/0.98      | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
% 3.33/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_11,plain,
% 3.33/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.33/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.33/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.98      | ~ l1_pre_topc(X1) ),
% 3.33/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1586,plain,
% 3.33/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.33/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.33/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.33/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1723,plain,
% 3.33/0.98      ( v2_compts_1(X0,X1) != iProver_top
% 3.33/0.98      | v2_compts_1(X0,X2) = iProver_top
% 3.33/0.98      | m1_pre_topc(X2,X1) != iProver_top
% 3.33/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 3.33/0.98      | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
% 3.33/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.33/0.98      inference(forward_subsumption_resolution,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_1582,c_1586]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_4452,plain,
% 3.33/0.98      ( v2_compts_1(X0,X1) != iProver_top
% 3.33/0.98      | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
% 3.33/0.98      | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
% 3.33/0.98      | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 3.33/0.98      | r1_tarski(X0,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top
% 3.33/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_2320,c_1723]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_6,plain,
% 3.33/0.98      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 3.33/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.33/0.98      | ~ l1_pre_topc(X0)
% 3.33/0.98      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 3.33/0.98      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 3.33/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_158,plain,
% 3.33/0.98      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.33/0.98      | ~ l1_pre_topc(X0)
% 3.33/0.98      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 3.33/0.98      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 3.33/0.98      inference(global_propositional_subsumption,[status(thm)],[c_6,c_7]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_159,plain,
% 3.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.98      | ~ l1_pre_topc(X1)
% 3.33/0.98      | ~ v1_pre_topc(k1_pre_topc(X1,X0))
% 3.33/0.98      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 3.33/0.98      inference(renaming,[status(thm)],[c_158]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_8,plain,
% 3.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.98      | ~ l1_pre_topc(X1)
% 3.33/0.98      | v1_pre_topc(k1_pre_topc(X1,X0)) ),
% 3.33/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_164,plain,
% 3.33/0.98      ( ~ l1_pre_topc(X1)
% 3.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.98      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 3.33/0.98      inference(global_propositional_subsumption,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_159,c_8]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_165,plain,
% 3.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.98      | ~ l1_pre_topc(X1)
% 3.33/0.98      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 3.33/0.98      inference(renaming,[status(thm)],[c_164]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1579,plain,
% 3.33/0.98      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
% 3.33/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.33/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_165]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1899,plain,
% 3.33/0.98      ( k2_struct_0(k1_pre_topc(sK2,sK3)) = sK3
% 3.33/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_1581,c_1579]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1808,plain,
% 3.33/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.33/0.98      | ~ l1_pre_topc(sK2)
% 3.33/0.98      | k2_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_165]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_2223,plain,
% 3.33/0.98      ( k2_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
% 3.33/0.98      inference(global_propositional_subsumption,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_1899,c_25,c_24,c_1808]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_4472,plain,
% 3.33/0.98      ( v2_compts_1(X0,X1) != iProver_top
% 3.33/0.98      | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
% 3.33/0.98      | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
% 3.33/0.98      | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 3.33/0.98      | r1_tarski(X0,sK3) != iProver_top
% 3.33/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.33/0.98      inference(light_normalisation,[status(thm)],[c_4452,c_2223]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3,plain,
% 3.33/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.33/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_2715,plain,
% 3.33/0.98      ( m1_subset_1(X0,k1_zfmisc_1(sK3)) | ~ r1_tarski(X0,sK3) ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_2716,plain,
% 3.33/0.98      ( m1_subset_1(X0,k1_zfmisc_1(sK3)) = iProver_top
% 3.33/0.98      | r1_tarski(X0,sK3) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_2715]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_6051,plain,
% 3.33/0.98      ( m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
% 3.33/0.98      | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
% 3.33/0.98      | v2_compts_1(X0,X1) != iProver_top
% 3.33/0.98      | r1_tarski(X0,sK3) != iProver_top
% 3.33/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.33/0.98      inference(global_propositional_subsumption,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_4472,c_2716]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_6052,plain,
% 3.33/0.98      ( v2_compts_1(X0,X1) != iProver_top
% 3.33/0.98      | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
% 3.33/0.98      | m1_pre_topc(k1_pre_topc(sK2,sK3),X1) != iProver_top
% 3.33/0.98      | r1_tarski(X0,sK3) != iProver_top
% 3.33/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.33/0.98      inference(renaming,[status(thm)],[c_6051]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_6062,plain,
% 3.33/0.98      ( v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
% 3.33/0.98      | v2_compts_1(X0,sK2) != iProver_top
% 3.33/0.98      | r1_tarski(X0,sK3) != iProver_top
% 3.33/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_3006,c_6052]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_6215,plain,
% 3.33/0.98      ( r1_tarski(X0,sK3) != iProver_top
% 3.33/0.98      | v2_compts_1(X0,sK2) != iProver_top
% 3.33/0.98      | v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top ),
% 3.33/0.98      inference(global_propositional_subsumption,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_6062,c_26]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_6216,plain,
% 3.33/0.98      ( v2_compts_1(X0,k1_pre_topc(sK2,sK3)) = iProver_top
% 3.33/0.98      | v2_compts_1(X0,sK2) != iProver_top
% 3.33/0.98      | r1_tarski(X0,sK3) != iProver_top ),
% 3.33/0.98      inference(renaming,[status(thm)],[c_6215]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_12,plain,
% 3.33/0.98      ( ~ v2_compts_1(k2_struct_0(X0),X0)
% 3.33/0.98      | v1_compts_1(X0)
% 3.33/0.98      | ~ l1_pre_topc(X0) ),
% 3.33/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_18,plain,
% 3.33/0.98      ( ~ sP0(X0,X1)
% 3.33/0.98      | ~ v2_compts_1(X0,X1)
% 3.33/0.98      | ~ v1_compts_1(k1_pre_topc(X1,X0)) ),
% 3.33/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_21,negated_conjecture,
% 3.33/0.98      ( sP0(sK3,sK2)
% 3.33/0.98      | ~ v2_compts_1(sK3,sK2)
% 3.33/0.98      | ~ v1_compts_1(k1_pre_topc(sK2,sK3)) ),
% 3.33/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_452,plain,
% 3.33/0.98      ( ~ v2_compts_1(X0,X1)
% 3.33/0.98      | ~ v2_compts_1(sK3,sK2)
% 3.33/0.98      | ~ v1_compts_1(k1_pre_topc(X1,X0))
% 3.33/0.98      | ~ v1_compts_1(k1_pre_topc(sK2,sK3))
% 3.33/0.98      | sK3 != X0
% 3.33/0.98      | sK2 != X1 ),
% 3.33/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_453,plain,
% 3.33/0.98      ( ~ v2_compts_1(sK3,sK2) | ~ v1_compts_1(k1_pre_topc(sK2,sK3)) ),
% 3.33/0.98      inference(unflattening,[status(thm)],[c_452]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_472,plain,
% 3.33/0.98      ( ~ v2_compts_1(k2_struct_0(X0),X0)
% 3.33/0.98      | ~ v2_compts_1(sK3,sK2)
% 3.33/0.98      | ~ l1_pre_topc(X0)
% 3.33/0.98      | k1_pre_topc(sK2,sK3) != X0 ),
% 3.33/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_453]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_473,plain,
% 3.33/0.98      ( ~ v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3))
% 3.33/0.98      | ~ v2_compts_1(sK3,sK2)
% 3.33/0.98      | ~ l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
% 3.33/0.98      inference(unflattening,[status(thm)],[c_472]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1578,plain,
% 3.33/0.98      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top
% 3.33/0.98      | v2_compts_1(sK3,sK2) != iProver_top
% 3.33/0.98      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_474,plain,
% 3.33/0.98      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top
% 3.33/0.98      | v2_compts_1(sK3,sK2) != iProver_top
% 3.33/0.98      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_9,plain,
% 3.33/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.33/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1774,plain,
% 3.33/0.98      ( ~ m1_pre_topc(k1_pre_topc(sK2,sK3),X0)
% 3.33/0.98      | ~ l1_pre_topc(X0)
% 3.33/0.98      | l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1775,plain,
% 3.33/0.98      ( m1_pre_topc(k1_pre_topc(sK2,sK3),X0) != iProver_top
% 3.33/0.98      | l1_pre_topc(X0) != iProver_top
% 3.33/0.98      | l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_1774]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1777,plain,
% 3.33/0.98      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 3.33/0.98      | l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top
% 3.33/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_1775]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1816,plain,
% 3.33/0.98      ( v2_compts_1(sK3,sK2) != iProver_top
% 3.33/0.98      | v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top ),
% 3.33/0.98      inference(global_propositional_subsumption,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_1578,c_26,c_27,c_474,c_1777,c_1801]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1817,plain,
% 3.33/0.98      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top
% 3.33/0.98      | v2_compts_1(sK3,sK2) != iProver_top ),
% 3.33/0.98      inference(renaming,[status(thm)],[c_1816]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_2227,plain,
% 3.33/0.98      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
% 3.33/0.98      | v2_compts_1(sK3,sK2) != iProver_top ),
% 3.33/0.98      inference(demodulation,[status(thm)],[c_2223,c_1817]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_6224,plain,
% 3.33/0.98      ( v2_compts_1(sK3,sK2) != iProver_top
% 3.33/0.98      | r1_tarski(sK3,sK3) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_6216,c_2227]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_6568,plain,
% 3.33/0.98      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.33/0.98      | r1_tarski(sK1(X0,sK3),u1_struct_0(X0)) = iProver_top
% 3.33/0.98      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
% 3.33/0.98      inference(global_propositional_subsumption,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_3192,c_2035,c_6224]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_6577,plain,
% 3.33/0.98      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 3.33/0.98      | r1_tarski(sK1(k1_pre_topc(sK2,sK3),sK3),sK3) = iProver_top
% 3.33/0.98      | r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_2320,c_6568]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_6616,plain,
% 3.33/0.98      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 3.33/0.98      | r1_tarski(sK1(k1_pre_topc(sK2,sK3),sK3),sK3) = iProver_top
% 3.33/0.98      | r1_tarski(sK3,sK3) != iProver_top ),
% 3.33/0.98      inference(light_normalisation,[status(thm)],[c_6577,c_2223]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_7146,plain,
% 3.33/0.98      ( r1_tarski(sK1(k1_pre_topc(sK2,sK3),sK3),sK3) = iProver_top ),
% 3.33/0.98      inference(global_propositional_subsumption,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_6616,c_26,c_27,c_1801,c_2035]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_0,plain,
% 3.33/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.33/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1595,plain,
% 3.33/0.98      ( X0 = X1
% 3.33/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.33/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_7151,plain,
% 3.33/0.98      ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
% 3.33/0.98      | r1_tarski(sK3,sK1(k1_pre_topc(sK2,sK3),sK3)) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_7146,c_1595]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_15,plain,
% 3.33/0.98      ( v2_compts_1(X0,X1)
% 3.33/0.98      | ~ m1_pre_topc(X2,X1)
% 3.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.98      | ~ r1_tarski(X0,k2_struct_0(X2))
% 3.33/0.98      | ~ l1_pre_topc(X1)
% 3.33/0.98      | sK1(X2,X0) = X0 ),
% 3.33/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1584,plain,
% 3.33/0.98      ( sK1(X0,X1) = X1
% 3.33/0.98      | v2_compts_1(X1,X2) = iProver_top
% 3.33/0.98      | m1_pre_topc(X0,X2) != iProver_top
% 3.33/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 3.33/0.98      | r1_tarski(X1,k2_struct_0(X0)) != iProver_top
% 3.33/0.98      | l1_pre_topc(X2) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3499,plain,
% 3.33/0.98      ( sK1(X0,sK3) = sK3
% 3.33/0.98      | v2_compts_1(sK3,sK2) = iProver_top
% 3.33/0.98      | m1_pre_topc(X0,sK2) != iProver_top
% 3.33/0.98      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
% 3.33/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_1581,c_1584]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_4158,plain,
% 3.33/0.98      ( r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
% 3.33/0.98      | m1_pre_topc(X0,sK2) != iProver_top
% 3.33/0.98      | v2_compts_1(sK3,sK2) = iProver_top
% 3.33/0.98      | sK1(X0,sK3) = sK3 ),
% 3.33/0.98      inference(global_propositional_subsumption,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_3499,c_26]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_4159,plain,
% 3.33/0.98      ( sK1(X0,sK3) = sK3
% 3.33/0.98      | v2_compts_1(sK3,sK2) = iProver_top
% 3.33/0.98      | m1_pre_topc(X0,sK2) != iProver_top
% 3.33/0.98      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
% 3.33/0.98      inference(renaming,[status(thm)],[c_4158]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_4168,plain,
% 3.33/0.98      ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
% 3.33/0.98      | v2_compts_1(sK3,sK2) = iProver_top
% 3.33/0.98      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 3.33/0.98      | r1_tarski(sK3,sK3) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_2223,c_4159]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_8154,plain,
% 3.33/0.98      ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3 ),
% 3.33/0.98      inference(global_propositional_subsumption,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_7151,c_26,c_27,c_1801,c_2035,c_4168,c_6224]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_14,plain,
% 3.33/0.98      ( v2_compts_1(X0,X1)
% 3.33/0.98      | ~ v2_compts_1(sK1(X2,X0),X2)
% 3.33/0.98      | ~ m1_pre_topc(X2,X1)
% 3.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.98      | ~ r1_tarski(X0,k2_struct_0(X2))
% 3.33/0.98      | ~ l1_pre_topc(X1) ),
% 3.33/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1585,plain,
% 3.33/0.98      ( v2_compts_1(X0,X1) = iProver_top
% 3.33/0.98      | v2_compts_1(sK1(X2,X0),X2) != iProver_top
% 3.33/0.98      | m1_pre_topc(X2,X1) != iProver_top
% 3.33/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.33/0.98      | r1_tarski(X0,k2_struct_0(X2)) != iProver_top
% 3.33/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3722,plain,
% 3.33/0.98      ( v2_compts_1(sK1(X0,sK3),X0) != iProver_top
% 3.33/0.98      | v2_compts_1(sK3,sK2) = iProver_top
% 3.33/0.98      | m1_pre_topc(X0,sK2) != iProver_top
% 3.33/0.98      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
% 3.33/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_1581,c_1585]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_4028,plain,
% 3.33/0.98      ( r1_tarski(sK3,k2_struct_0(X0)) != iProver_top
% 3.33/0.98      | m1_pre_topc(X0,sK2) != iProver_top
% 3.33/0.98      | v2_compts_1(sK3,sK2) = iProver_top
% 3.33/0.98      | v2_compts_1(sK1(X0,sK3),X0) != iProver_top ),
% 3.33/0.98      inference(global_propositional_subsumption,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_3722,c_26]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_4029,plain,
% 3.33/0.98      ( v2_compts_1(sK1(X0,sK3),X0) != iProver_top
% 3.33/0.98      | v2_compts_1(sK3,sK2) = iProver_top
% 3.33/0.98      | m1_pre_topc(X0,sK2) != iProver_top
% 3.33/0.98      | r1_tarski(sK3,k2_struct_0(X0)) != iProver_top ),
% 3.33/0.98      inference(renaming,[status(thm)],[c_4028]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_8161,plain,
% 3.33/0.98      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
% 3.33/0.98      | v2_compts_1(sK3,sK2) = iProver_top
% 3.33/0.98      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 3.33/0.98      | r1_tarski(sK3,k2_struct_0(k1_pre_topc(sK2,sK3))) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_8154,c_4029]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_8179,plain,
% 3.33/0.98      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
% 3.33/0.98      | v2_compts_1(sK3,sK2) = iProver_top
% 3.33/0.98      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 3.33/0.98      | r1_tarski(sK3,sK3) != iProver_top ),
% 3.33/0.98      inference(light_normalisation,[status(thm)],[c_8161,c_2223]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_13,plain,
% 3.33/0.98      ( v2_compts_1(k2_struct_0(X0),X0)
% 3.33/0.98      | ~ v1_compts_1(X0)
% 3.33/0.98      | ~ l1_pre_topc(X0) ),
% 3.33/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_19,plain,
% 3.33/0.98      ( ~ sP0(X0,X1)
% 3.33/0.98      | v2_compts_1(X0,X1)
% 3.33/0.98      | v1_compts_1(k1_pre_topc(X1,X0)) ),
% 3.33/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_22,negated_conjecture,
% 3.33/0.98      ( sP0(sK3,sK2)
% 3.33/0.98      | v2_compts_1(sK3,sK2)
% 3.33/0.98      | v1_compts_1(k1_pre_topc(sK2,sK3)) ),
% 3.33/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_425,plain,
% 3.33/0.98      ( v2_compts_1(X0,X1)
% 3.33/0.98      | v2_compts_1(sK3,sK2)
% 3.33/0.98      | v1_compts_1(k1_pre_topc(X1,X0))
% 3.33/0.98      | v1_compts_1(k1_pre_topc(sK2,sK3))
% 3.33/0.98      | sK3 != X0
% 3.33/0.98      | sK2 != X1 ),
% 3.33/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_426,plain,
% 3.33/0.98      ( v2_compts_1(sK3,sK2) | v1_compts_1(k1_pre_topc(sK2,sK3)) ),
% 3.33/0.98      inference(unflattening,[status(thm)],[c_425]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_485,plain,
% 3.33/0.98      ( v2_compts_1(k2_struct_0(X0),X0)
% 3.33/0.98      | v2_compts_1(sK3,sK2)
% 3.33/0.98      | ~ l1_pre_topc(X0)
% 3.33/0.98      | k1_pre_topc(sK2,sK3) != X0 ),
% 3.33/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_426]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_486,plain,
% 3.33/0.98      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3))
% 3.33/0.98      | v2_compts_1(sK3,sK2)
% 3.33/0.98      | ~ l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
% 3.33/0.98      inference(unflattening,[status(thm)],[c_485]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1577,plain,
% 3.33/0.98      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
% 3.33/0.98      | v2_compts_1(sK3,sK2) = iProver_top
% 3.33/0.98      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_487,plain,
% 3.33/0.98      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
% 3.33/0.98      | v2_compts_1(sK3,sK2) = iProver_top
% 3.33/0.98      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1829,plain,
% 3.33/0.98      ( v2_compts_1(sK3,sK2) = iProver_top
% 3.33/0.98      | v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top ),
% 3.33/0.98      inference(global_propositional_subsumption,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_1577,c_26,c_27,c_487,c_1777,c_1801]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1830,plain,
% 3.33/0.98      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
% 3.33/0.98      | v2_compts_1(sK3,sK2) = iProver_top ),
% 3.33/0.98      inference(renaming,[status(thm)],[c_1829]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_2226,plain,
% 3.33/0.98      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
% 3.33/0.98      | v2_compts_1(sK3,sK2) = iProver_top ),
% 3.33/0.98      inference(demodulation,[status(thm)],[c_2223,c_1830]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(contradiction,plain,
% 3.33/0.98      ( $false ),
% 3.33/0.98      inference(minisat,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_8179,c_6224,c_2226,c_2035,c_1801,c_27,c_26]) ).
% 3.33/0.98  
% 3.33/0.98  
% 3.33/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.33/0.98  
% 3.33/0.98  ------                               Statistics
% 3.33/0.98  
% 3.33/0.98  ------ General
% 3.33/0.98  
% 3.33/0.98  abstr_ref_over_cycles:                  0
% 3.33/0.98  abstr_ref_under_cycles:                 0
% 3.33/0.98  gc_basic_clause_elim:                   0
% 3.33/0.98  forced_gc_time:                         0
% 3.33/0.98  parsing_time:                           0.01
% 3.33/0.98  unif_index_cands_time:                  0.
% 3.33/0.98  unif_index_add_time:                    0.
% 3.33/0.98  orderings_time:                         0.
% 3.33/0.98  out_proof_time:                         0.023
% 3.33/0.98  total_time:                             0.253
% 3.33/0.98  num_of_symbols:                         47
% 3.33/0.98  num_of_terms:                           4967
% 3.33/0.98  
% 3.33/0.98  ------ Preprocessing
% 3.33/0.98  
% 3.33/0.98  num_of_splits:                          0
% 3.33/0.98  num_of_split_atoms:                     0
% 3.33/0.98  num_of_reused_defs:                     0
% 3.33/0.98  num_eq_ax_congr_red:                    12
% 3.33/0.98  num_of_sem_filtered_clauses:            1
% 3.33/0.98  num_of_subtypes:                        0
% 3.33/0.98  monotx_restored_types:                  0
% 3.33/0.98  sat_num_of_epr_types:                   0
% 3.33/0.98  sat_num_of_non_cyclic_types:            0
% 3.33/0.98  sat_guarded_non_collapsed_types:        0
% 3.33/0.98  num_pure_diseq_elim:                    0
% 3.33/0.98  simp_replaced_by:                       0
% 3.33/0.98  res_preprocessed:                       110
% 3.33/0.98  prep_upred:                             0
% 3.33/0.98  prep_unflattend:                        50
% 3.33/0.98  smt_new_axioms:                         0
% 3.33/0.98  pred_elim_cands:                        6
% 3.33/0.98  pred_elim:                              2
% 3.33/0.98  pred_elim_cl:                           5
% 3.33/0.98  pred_elim_cycles:                       6
% 3.33/0.98  merged_defs:                            8
% 3.33/0.98  merged_defs_ncl:                        0
% 3.33/0.98  bin_hyper_res:                          8
% 3.33/0.98  prep_cycles:                            4
% 3.33/0.98  pred_elim_time:                         0.024
% 3.33/0.98  splitting_time:                         0.
% 3.33/0.98  sem_filter_time:                        0.
% 3.33/0.98  monotx_time:                            0.001
% 3.33/0.98  subtype_inf_time:                       0.
% 3.33/0.98  
% 3.33/0.98  ------ Problem properties
% 3.33/0.98  
% 3.33/0.98  clauses:                                20
% 3.33/0.98  conjectures:                            2
% 3.33/0.98  epr:                                    5
% 3.33/0.98  horn:                                   17
% 3.33/0.98  ground:                                 5
% 3.33/0.98  unary:                                  3
% 3.33/0.98  binary:                                 3
% 3.33/0.98  lits:                                   67
% 3.33/0.98  lits_eq:                                7
% 3.33/0.98  fd_pure:                                0
% 3.33/0.98  fd_pseudo:                              0
% 3.33/0.98  fd_cond:                                0
% 3.33/0.98  fd_pseudo_cond:                         1
% 3.33/0.98  ac_symbols:                             0
% 3.33/0.98  
% 3.33/0.98  ------ Propositional Solver
% 3.33/0.98  
% 3.33/0.98  prop_solver_calls:                      30
% 3.33/0.98  prop_fast_solver_calls:                 1198
% 3.33/0.98  smt_solver_calls:                       0
% 3.33/0.98  smt_fast_solver_calls:                  0
% 3.33/0.98  prop_num_of_clauses:                    2674
% 3.33/0.98  prop_preprocess_simplified:             6279
% 3.33/0.98  prop_fo_subsumed:                       42
% 3.33/0.98  prop_solver_time:                       0.
% 3.33/0.98  smt_solver_time:                        0.
% 3.33/0.98  smt_fast_solver_time:                   0.
% 3.33/0.98  prop_fast_solver_time:                  0.
% 3.33/0.98  prop_unsat_core_time:                   0.
% 3.33/0.98  
% 3.33/0.98  ------ QBF
% 3.33/0.98  
% 3.33/0.98  qbf_q_res:                              0
% 3.33/0.98  qbf_num_tautologies:                    0
% 3.33/0.98  qbf_prep_cycles:                        0
% 3.33/0.98  
% 3.33/0.98  ------ BMC1
% 3.33/0.98  
% 3.33/0.98  bmc1_current_bound:                     -1
% 3.33/0.98  bmc1_last_solved_bound:                 -1
% 3.33/0.98  bmc1_unsat_core_size:                   -1
% 3.33/0.98  bmc1_unsat_core_parents_size:           -1
% 3.33/0.98  bmc1_merge_next_fun:                    0
% 3.33/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.33/0.98  
% 3.33/0.98  ------ Instantiation
% 3.33/0.98  
% 3.33/0.98  inst_num_of_clauses:                    804
% 3.33/0.98  inst_num_in_passive:                    144
% 3.33/0.98  inst_num_in_active:                     408
% 3.33/0.98  inst_num_in_unprocessed:                253
% 3.33/0.98  inst_num_of_loops:                      430
% 3.33/0.98  inst_num_of_learning_restarts:          0
% 3.33/0.98  inst_num_moves_active_passive:          18
% 3.33/0.98  inst_lit_activity:                      0
% 3.33/0.98  inst_lit_activity_moves:                0
% 3.33/0.98  inst_num_tautologies:                   0
% 3.33/0.98  inst_num_prop_implied:                  0
% 3.33/0.98  inst_num_existing_simplified:           0
% 3.33/0.98  inst_num_eq_res_simplified:             0
% 3.33/0.98  inst_num_child_elim:                    0
% 3.33/0.98  inst_num_of_dismatching_blockings:      383
% 3.33/0.98  inst_num_of_non_proper_insts:           1001
% 3.33/0.98  inst_num_of_duplicates:                 0
% 3.33/0.98  inst_inst_num_from_inst_to_res:         0
% 3.33/0.98  inst_dismatching_checking_time:         0.
% 3.33/0.98  
% 3.33/0.98  ------ Resolution
% 3.33/0.98  
% 3.33/0.98  res_num_of_clauses:                     0
% 3.33/0.98  res_num_in_passive:                     0
% 3.33/0.98  res_num_in_active:                      0
% 3.33/0.98  res_num_of_loops:                       114
% 3.33/0.98  res_forward_subset_subsumed:            95
% 3.33/0.98  res_backward_subset_subsumed:           8
% 3.33/0.98  res_forward_subsumed:                   0
% 3.33/0.98  res_backward_subsumed:                  0
% 3.33/0.98  res_forward_subsumption_resolution:     1
% 3.33/0.98  res_backward_subsumption_resolution:    0
% 3.33/0.98  res_clause_to_clause_subsumption:       563
% 3.33/0.98  res_orphan_elimination:                 0
% 3.33/0.98  res_tautology_del:                      123
% 3.33/0.98  res_num_eq_res_simplified:              0
% 3.33/0.98  res_num_sel_changes:                    0
% 3.33/0.98  res_moves_from_active_to_pass:          0
% 3.33/0.98  
% 3.33/0.98  ------ Superposition
% 3.33/0.98  
% 3.33/0.98  sup_time_total:                         0.
% 3.33/0.98  sup_time_generating:                    0.
% 3.33/0.98  sup_time_sim_full:                      0.
% 3.33/0.98  sup_time_sim_immed:                     0.
% 3.33/0.98  
% 3.33/0.98  sup_num_of_clauses:                     183
% 3.33/0.98  sup_num_in_active:                      81
% 3.33/0.98  sup_num_in_passive:                     102
% 3.33/0.98  sup_num_of_loops:                       84
% 3.33/0.98  sup_fw_superposition:                   102
% 3.33/0.98  sup_bw_superposition:                   101
% 3.33/0.98  sup_immediate_simplified:               40
% 3.33/0.98  sup_given_eliminated:                   0
% 3.33/0.98  comparisons_done:                       0
% 3.33/0.98  comparisons_avoided:                    0
% 3.33/0.98  
% 3.33/0.98  ------ Simplifications
% 3.33/0.98  
% 3.33/0.98  
% 3.33/0.98  sim_fw_subset_subsumed:                 5
% 3.33/0.98  sim_bw_subset_subsumed:                 1
% 3.33/0.98  sim_fw_subsumed:                        6
% 3.33/0.98  sim_bw_subsumed:                        4
% 3.33/0.98  sim_fw_subsumption_res:                 2
% 3.33/0.98  sim_bw_subsumption_res:                 1
% 3.33/0.98  sim_tautology_del:                      4
% 3.33/0.98  sim_eq_tautology_del:                   7
% 3.33/0.98  sim_eq_res_simp:                        0
% 3.33/0.98  sim_fw_demodulated:                     0
% 3.33/0.98  sim_bw_demodulated:                     4
% 3.33/0.98  sim_light_normalised:                   25
% 3.33/0.98  sim_joinable_taut:                      0
% 3.33/0.98  sim_joinable_simp:                      0
% 3.33/0.98  sim_ac_normalised:                      0
% 3.33/0.98  sim_smt_subsumption:                    0
% 3.33/0.98  
%------------------------------------------------------------------------------
