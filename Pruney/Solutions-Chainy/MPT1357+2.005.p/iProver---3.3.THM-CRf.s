%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:55 EST 2020

% Result     : Theorem 11.76s
% Output     : CNFRefutation 11.76s
% Verified   : 
% Statistics : Number of formulae       :  160 (2918 expanded)
%              Number of clauses        :   96 ( 766 expanded)
%              Number of leaves         :   16 ( 681 expanded)
%              Depth                    :   27
%              Number of atoms          :  627 (16569 expanded)
%              Number of equality atoms :  226 (3259 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
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
    inference(pure_predicate_removal,[],[f13])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ( ( v2_compts_1(X1,X0)
        <~> v1_compts_1(k1_pre_topc(X0,X1)) )
        & k1_xboole_0 = X1 )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 != X1 )
            | sP0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f28,f29])).

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
    inference(nnf_transformation,[],[f30])).

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

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(nnf_transformation,[],[f27])).

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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | sK1(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ~ v2_compts_1(k2_struct_0(X0),X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f29])).

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

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(k1_pre_topc(X1,X0))
      | ~ v2_compts_1(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK2,sK3))
    | ~ v2_compts_1(sK3,sK2)
    | sP0(sK3,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f55,plain,(
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

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( v2_compts_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X4,X0)
      | ~ r1_tarski(X4,k2_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f53,plain,(
    ! [X0] :
      ( v2_compts_1(k2_struct_0(X0),X0)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X1,X0))
      | v2_compts_1(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,
    ( v1_compts_1(k1_pre_topc(sK2,sK3))
    | v2_compts_1(sK3,sK2)
    | sP0(sK3,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(sK1(X1,X2),X1)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1212,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1216,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1852,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1216])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_24,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1404,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1405,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1404])).

cnf(c_2058,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1852,c_23,c_24,c_1405])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1215,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2063,plain,
    ( l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2058,c_1215])).

cnf(c_1449,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
    | l1_pre_topc(k1_pre_topc(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1450,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1449])).

cnf(c_2344,plain,
    ( l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2063,c_23,c_24,c_1405,c_1450])).

cnf(c_5,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_246,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_5,c_3])).

cnf(c_1210,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_246])).

cnf(c_2862,plain,
    ( u1_struct_0(k1_pre_topc(sK2,sK3)) = k2_struct_0(k1_pre_topc(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2344,c_1210])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1214,plain,
    ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1738,plain,
    ( u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1214])).

cnf(c_1409,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2006,plain,
    ( u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1738,c_22,c_21,c_1409])).

cnf(c_2864,plain,
    ( k2_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_2862,c_2006])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1213,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1871,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1213])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_12,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1(X2,X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_309,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | X0 != X3
    | sK1(X2,X0) = X0
    | k2_struct_0(X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_12])).

cnf(c_310,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | sK1(X2,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_1207,plain,
    ( sK1(X0,X1) = X1
    | v2_compts_1(X1,X2) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X0))) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_2611,plain,
    ( sK1(X0,sK3) = sK3
    | v2_compts_1(sK3,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(X0))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1871,c_1207])).

cnf(c_5326,plain,
    ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
    | v2_compts_1(sK3,X0) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2864,c_2611])).

cnf(c_2609,plain,
    ( sK1(X0,sK3) = sK3
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(X0))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1207])).

cnf(c_3217,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(X0))) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | sK1(X0,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2609,c_23])).

cnf(c_3218,plain,
    ( sK1(X0,sK3) = sK3
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(X0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3217])).

cnf(c_3401,plain,
    ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2864,c_3218])).

cnf(c_5197,plain,
    ( v2_compts_1(sK3,sK2) = iProver_top
    | sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3401,c_23,c_24,c_1405])).

cnf(c_5198,plain,
    ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5197])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1217,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1224,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1217,c_0])).

cnf(c_5204,plain,
    ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
    | v2_compts_1(sK3,sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5198,c_1224])).

cnf(c_9,plain,
    ( ~ v2_compts_1(k2_struct_0(X0),X0)
    | v1_compts_1(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1)
    | ~ v2_compts_1(X0,X1)
    | ~ v1_compts_1(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_18,negated_conjecture,
    ( sP0(sK3,sK2)
    | ~ v2_compts_1(sK3,sK2)
    | ~ v1_compts_1(k1_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_459,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK3,sK2)
    | ~ v1_compts_1(k1_pre_topc(X1,X0))
    | ~ v1_compts_1(k1_pre_topc(sK2,sK3))
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_460,plain,
    ( ~ v2_compts_1(sK3,sK2)
    | ~ v1_compts_1(k1_pre_topc(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_479,plain,
    ( ~ v2_compts_1(k2_struct_0(X0),X0)
    | ~ v2_compts_1(sK3,sK2)
    | ~ l1_pre_topc(X0)
    | k1_pre_topc(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_460])).

cnf(c_480,plain,
    ( ~ v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3))
    | ~ v2_compts_1(sK3,sK2)
    | ~ l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_1205,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_3388,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2864,c_1205])).

cnf(c_14072,plain,
    ( v2_compts_1(sK3,sK2) != iProver_top
    | v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3388,c_23,c_24,c_1405,c_1450])).

cnf(c_14073,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_14072])).

cnf(c_14,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_260,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | X0 != X3
    | k2_struct_0(X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_14])).

cnf(c_261,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_277,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_261,c_8])).

cnf(c_1209,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X2))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_277])).

cnf(c_5517,plain,
    ( v2_compts_1(u1_struct_0(X0),X1) != iProver_top
    | v2_compts_1(u1_struct_0(X0),X0) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(X0))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1224,c_1209])).

cnf(c_18882,plain,
    ( v2_compts_1(u1_struct_0(k1_pre_topc(sK2,sK3)),X0) != iProver_top
    | v2_compts_1(u1_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),X0) != iProver_top
    | m1_subset_1(u1_struct_0(k1_pre_topc(sK2,sK3)),k1_zfmisc_1(sK3)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2864,c_5517])).

cnf(c_18888,plain,
    ( v2_compts_1(sK3,X0) != iProver_top
    | v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18882,c_2006])).

cnf(c_10,plain,
    ( v2_compts_1(k2_struct_0(X0),X0)
    | ~ v1_compts_1(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1)
    | v2_compts_1(X0,X1)
    | v1_compts_1(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_19,negated_conjecture,
    ( sP0(sK3,sK2)
    | v2_compts_1(sK3,sK2)
    | v1_compts_1(k1_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_432,plain,
    ( v2_compts_1(X0,X1)
    | v2_compts_1(sK3,sK2)
    | v1_compts_1(k1_pre_topc(X1,X0))
    | v1_compts_1(k1_pre_topc(sK2,sK3))
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_433,plain,
    ( v2_compts_1(sK3,sK2)
    | v1_compts_1(k1_pre_topc(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_492,plain,
    ( v2_compts_1(k2_struct_0(X0),X0)
    | v2_compts_1(sK3,sK2)
    | ~ l1_pre_topc(X0)
    | k1_pre_topc(sK2,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_433])).

cnf(c_493,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3))
    | v2_compts_1(sK3,sK2)
    | ~ l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_1204,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_493])).

cnf(c_494,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_493])).

cnf(c_1481,plain,
    ( v2_compts_1(sK3,sK2) = iProver_top
    | v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1204,c_23,c_24,c_494,c_1405,c_1450])).

cnf(c_1482,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_1481])).

cnf(c_3387,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2864,c_1482])).

cnf(c_18952,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
    | v2_compts_1(sK3,sK2) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_18888])).

cnf(c_19149,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
    | v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18888,c_23,c_24,c_1405,c_3387,c_18952])).

cnf(c_19150,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_19149])).

cnf(c_19155,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19150,c_1224])).

cnf(c_42408,plain,
    ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5326,c_5204,c_14073,c_19155])).

cnf(c_11,plain,
    ( v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK1(X2,X0),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ r1_tarski(X0,k2_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_333,plain,
    ( v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK1(X2,X0),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | X0 != X3
    | k2_struct_0(X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_334,plain,
    ( v2_compts_1(X0,X1)
    | ~ v2_compts_1(sK1(X2,X0),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_1206,plain,
    ( v2_compts_1(X0,X1) = iProver_top
    | v2_compts_1(sK1(X2,X0),X2) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X2))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_334])).

cnf(c_1620,plain,
    ( v2_compts_1(sK1(X0,sK3),X0) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(X0))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1206])).

cnf(c_2236,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(X0))) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | v2_compts_1(sK1(X0,sK3),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1620,c_23])).

cnf(c_2237,plain,
    ( v2_compts_1(sK1(X0,sK3),X0) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(X0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2236])).

cnf(c_42413,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(k1_pre_topc(sK2,sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_42408,c_2237])).

cnf(c_42448,plain,
    ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
    | v2_compts_1(sK3,sK2) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_42413,c_2864])).

cnf(c_44484,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42448,c_23,c_24,c_1405,c_14073,c_19155])).

cnf(c_44489,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_44484,c_1224])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:22:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.76/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.76/2.00  
% 11.76/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.76/2.00  
% 11.76/2.00  ------  iProver source info
% 11.76/2.00  
% 11.76/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.76/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.76/2.00  git: non_committed_changes: false
% 11.76/2.00  git: last_make_outside_of_git: false
% 11.76/2.00  
% 11.76/2.00  ------ 
% 11.76/2.00  ------ Parsing...
% 11.76/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.76/2.00  
% 11.76/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.76/2.00  
% 11.76/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.76/2.00  
% 11.76/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.76/2.00  ------ Proving...
% 11.76/2.00  ------ Problem Properties 
% 11.76/2.00  
% 11.76/2.00  
% 11.76/2.00  clauses                                 16
% 11.76/2.00  conjectures                             2
% 11.76/2.00  EPR                                     3
% 11.76/2.00  Horn                                    13
% 11.76/2.00  unary                                   4
% 11.76/2.00  binary                                  2
% 11.76/2.00  lits                                    51
% 11.76/2.00  lits eq                                 6
% 11.76/2.00  fd_pure                                 0
% 11.76/2.00  fd_pseudo                               0
% 11.76/2.00  fd_cond                                 0
% 11.76/2.00  fd_pseudo_cond                          0
% 11.76/2.00  AC symbols                              0
% 11.76/2.00  
% 11.76/2.00  ------ Input Options Time Limit: Unbounded
% 11.76/2.00  
% 11.76/2.00  
% 11.76/2.00  ------ 
% 11.76/2.00  Current options:
% 11.76/2.00  ------ 
% 11.76/2.00  
% 11.76/2.00  
% 11.76/2.00  
% 11.76/2.00  
% 11.76/2.00  ------ Proving...
% 11.76/2.00  
% 11.76/2.00  
% 11.76/2.00  % SZS status Theorem for theBenchmark.p
% 11.76/2.00  
% 11.76/2.00   Resolution empty clause
% 11.76/2.00  
% 11.76/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.76/2.00  
% 11.76/2.00  fof(f12,conjecture,(
% 11.76/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 11.76/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.76/2.00  
% 11.76/2.00  fof(f13,negated_conjecture,(
% 11.76/2.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 11.76/2.00    inference(negated_conjecture,[],[f12])).
% 11.76/2.00  
% 11.76/2.00  fof(f15,plain,(
% 11.76/2.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 11.76/2.00    inference(pure_predicate_removal,[],[f13])).
% 11.76/2.00  
% 11.76/2.00  fof(f28,plain,(
% 11.76/2.00    ? [X0] : (? [X1] : ((((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 != X1) | ((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 11.76/2.00    inference(ennf_transformation,[],[f15])).
% 11.76/2.00  
% 11.76/2.00  fof(f29,plain,(
% 11.76/2.00    ! [X1,X0] : (((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 = X1) | ~sP0(X1,X0))),
% 11.76/2.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 11.76/2.00  
% 11.76/2.00  fof(f30,plain,(
% 11.76/2.00    ? [X0] : (? [X1] : ((((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 11.76/2.00    inference(definition_folding,[],[f28,f29])).
% 11.76/2.00  
% 11.76/2.00  fof(f39,plain,(
% 11.76/2.00    ? [X0] : (? [X1] : (((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0))) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 11.76/2.00    inference(nnf_transformation,[],[f30])).
% 11.76/2.00  
% 11.76/2.00  fof(f40,plain,(
% 11.76/2.00    ? [X0] : (? [X1] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 11.76/2.00    inference(flattening,[],[f39])).
% 11.76/2.00  
% 11.76/2.00  fof(f42,plain,(
% 11.76/2.00    ( ! [X0] : (? [X1] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((((~v1_compts_1(k1_pre_topc(X0,sK3)) | ~v2_compts_1(sK3,X0)) & (v1_compts_1(k1_pre_topc(X0,sK3)) | v2_compts_1(sK3,X0)) & k1_xboole_0 != sK3) | sP0(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.76/2.00    introduced(choice_axiom,[])).
% 11.76/2.00  
% 11.76/2.00  fof(f41,plain,(
% 11.76/2.00    ? [X0] : (? [X1] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 != X1) | sP0(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((((~v1_compts_1(k1_pre_topc(sK2,X1)) | ~v2_compts_1(X1,sK2)) & (v1_compts_1(k1_pre_topc(sK2,X1)) | v2_compts_1(X1,sK2)) & k1_xboole_0 != X1) | sP0(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 11.76/2.00    introduced(choice_axiom,[])).
% 11.76/2.00  
% 11.76/2.00  fof(f43,plain,(
% 11.76/2.00    ((((~v1_compts_1(k1_pre_topc(sK2,sK3)) | ~v2_compts_1(sK3,sK2)) & (v1_compts_1(k1_pre_topc(sK2,sK3)) | v2_compts_1(sK3,sK2)) & k1_xboole_0 != sK3) | sP0(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 11.76/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).
% 11.76/2.00  
% 11.76/2.00  fof(f63,plain,(
% 11.76/2.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 11.76/2.00    inference(cnf_transformation,[],[f43])).
% 11.76/2.00  
% 11.76/2.00  fof(f5,axiom,(
% 11.76/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 11.76/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.76/2.00  
% 11.76/2.00  fof(f16,plain,(
% 11.76/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 11.76/2.00    inference(pure_predicate_removal,[],[f5])).
% 11.76/2.00  
% 11.76/2.00  fof(f19,plain,(
% 11.76/2.00    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.76/2.00    inference(ennf_transformation,[],[f16])).
% 11.76/2.00  
% 11.76/2.00  fof(f20,plain,(
% 11.76/2.00    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.76/2.00    inference(flattening,[],[f19])).
% 11.76/2.00  
% 11.76/2.00  fof(f48,plain,(
% 11.76/2.00    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.76/2.00    inference(cnf_transformation,[],[f20])).
% 11.76/2.00  
% 11.76/2.00  fof(f62,plain,(
% 11.76/2.00    l1_pre_topc(sK2)),
% 11.76/2.00    inference(cnf_transformation,[],[f43])).
% 11.76/2.00  
% 11.76/2.00  fof(f7,axiom,(
% 11.76/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 11.76/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.76/2.00  
% 11.76/2.00  fof(f22,plain,(
% 11.76/2.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.76/2.00    inference(ennf_transformation,[],[f7])).
% 11.76/2.00  
% 11.76/2.00  fof(f50,plain,(
% 11.76/2.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.76/2.00    inference(cnf_transformation,[],[f22])).
% 11.76/2.00  
% 11.76/2.00  fof(f6,axiom,(
% 11.76/2.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 11.76/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.76/2.00  
% 11.76/2.00  fof(f21,plain,(
% 11.76/2.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 11.76/2.00    inference(ennf_transformation,[],[f6])).
% 11.76/2.00  
% 11.76/2.00  fof(f49,plain,(
% 11.76/2.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 11.76/2.00    inference(cnf_transformation,[],[f21])).
% 11.76/2.00  
% 11.76/2.00  fof(f4,axiom,(
% 11.76/2.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 11.76/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.76/2.00  
% 11.76/2.00  fof(f18,plain,(
% 11.76/2.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 11.76/2.00    inference(ennf_transformation,[],[f4])).
% 11.76/2.00  
% 11.76/2.00  fof(f47,plain,(
% 11.76/2.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 11.76/2.00    inference(cnf_transformation,[],[f18])).
% 11.76/2.00  
% 11.76/2.00  fof(f8,axiom,(
% 11.76/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 11.76/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.76/2.00  
% 11.76/2.00  fof(f23,plain,(
% 11.76/2.00    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.76/2.00    inference(ennf_transformation,[],[f8])).
% 11.76/2.00  
% 11.76/2.00  fof(f51,plain,(
% 11.76/2.00    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.76/2.00    inference(cnf_transformation,[],[f23])).
% 11.76/2.00  
% 11.76/2.00  fof(f9,axiom,(
% 11.76/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 11.76/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.76/2.00  
% 11.76/2.00  fof(f24,plain,(
% 11.76/2.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.76/2.00    inference(ennf_transformation,[],[f9])).
% 11.76/2.00  
% 11.76/2.00  fof(f52,plain,(
% 11.76/2.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.76/2.00    inference(cnf_transformation,[],[f24])).
% 11.76/2.00  
% 11.76/2.00  fof(f3,axiom,(
% 11.76/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.76/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.76/2.00  
% 11.76/2.00  fof(f14,plain,(
% 11.76/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 11.76/2.00    inference(unused_predicate_definition_removal,[],[f3])).
% 11.76/2.00  
% 11.76/2.00  fof(f17,plain,(
% 11.76/2.00    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 11.76/2.00    inference(ennf_transformation,[],[f14])).
% 11.76/2.00  
% 11.76/2.00  fof(f46,plain,(
% 11.76/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.76/2.00    inference(cnf_transformation,[],[f17])).
% 11.76/2.00  
% 11.76/2.00  fof(f11,axiom,(
% 11.76/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 11.76/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.76/2.00  
% 11.76/2.00  fof(f26,plain,(
% 11.76/2.00    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.76/2.00    inference(ennf_transformation,[],[f11])).
% 11.76/2.00  
% 11.76/2.00  fof(f27,plain,(
% 11.76/2.00    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.76/2.00    inference(flattening,[],[f26])).
% 11.76/2.00  
% 11.76/2.00  fof(f32,plain,(
% 11.76/2.00    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.76/2.00    inference(nnf_transformation,[],[f27])).
% 11.76/2.00  
% 11.76/2.00  fof(f33,plain,(
% 11.76/2.00    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.76/2.00    inference(rectify,[],[f32])).
% 11.76/2.00  
% 11.76/2.00  fof(f34,plain,(
% 11.76/2.00    ! [X2,X1] : (? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v2_compts_1(sK1(X1,X2),X1) & sK1(X1,X2) = X2 & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 11.76/2.00    introduced(choice_axiom,[])).
% 11.76/2.00  
% 11.76/2.00  fof(f35,plain,(
% 11.76/2.00    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | (~v2_compts_1(sK1(X1,X2),X1) & sK1(X1,X2) = X2 & m1_subset_1(sK1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.76/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 11.76/2.00  
% 11.76/2.00  fof(f57,plain,(
% 11.76/2.00    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | sK1(X1,X2) = X2 | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.76/2.00    inference(cnf_transformation,[],[f35])).
% 11.76/2.00  
% 11.76/2.00  fof(f2,axiom,(
% 11.76/2.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 11.76/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.76/2.00  
% 11.76/2.00  fof(f45,plain,(
% 11.76/2.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 11.76/2.00    inference(cnf_transformation,[],[f2])).
% 11.76/2.00  
% 11.76/2.00  fof(f1,axiom,(
% 11.76/2.00    ! [X0] : k2_subset_1(X0) = X0),
% 11.76/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.76/2.00  
% 11.76/2.00  fof(f44,plain,(
% 11.76/2.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 11.76/2.00    inference(cnf_transformation,[],[f1])).
% 11.76/2.00  
% 11.76/2.00  fof(f10,axiom,(
% 11.76/2.00    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 11.76/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.76/2.00  
% 11.76/2.00  fof(f25,plain,(
% 11.76/2.00    ! [X0] : ((v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)) | ~l1_pre_topc(X0))),
% 11.76/2.00    inference(ennf_transformation,[],[f10])).
% 11.76/2.00  
% 11.76/2.00  fof(f31,plain,(
% 11.76/2.00    ! [X0] : (((v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0)) & (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 11.76/2.00    inference(nnf_transformation,[],[f25])).
% 11.76/2.00  
% 11.76/2.00  fof(f54,plain,(
% 11.76/2.00    ( ! [X0] : (v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0)) )),
% 11.76/2.00    inference(cnf_transformation,[],[f31])).
% 11.76/2.00  
% 11.76/2.00  fof(f36,plain,(
% 11.76/2.00    ! [X1,X0] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0))) & k1_xboole_0 = X1) | ~sP0(X1,X0))),
% 11.76/2.00    inference(nnf_transformation,[],[f29])).
% 11.76/2.00  
% 11.76/2.00  fof(f37,plain,(
% 11.76/2.00    ! [X1,X0] : (((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 = X1) | ~sP0(X1,X0))),
% 11.76/2.00    inference(flattening,[],[f36])).
% 11.76/2.00  
% 11.76/2.00  fof(f38,plain,(
% 11.76/2.00    ! [X0,X1] : (((~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1)) & (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1)) & k1_xboole_0 = X0) | ~sP0(X0,X1))),
% 11.76/2.00    inference(rectify,[],[f37])).
% 11.76/2.00  
% 11.76/2.00  fof(f61,plain,(
% 11.76/2.00    ( ! [X0,X1] : (~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1) | ~sP0(X0,X1)) )),
% 11.76/2.00    inference(cnf_transformation,[],[f38])).
% 11.76/2.00  
% 11.76/2.00  fof(f66,plain,(
% 11.76/2.00    ~v1_compts_1(k1_pre_topc(sK2,sK3)) | ~v2_compts_1(sK3,sK2) | sP0(sK3,sK2)),
% 11.76/2.00    inference(cnf_transformation,[],[f43])).
% 11.76/2.00  
% 11.76/2.00  fof(f55,plain,(
% 11.76/2.00    ( ! [X4,X2,X0,X1] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.76/2.00    inference(cnf_transformation,[],[f35])).
% 11.76/2.00  
% 11.76/2.00  fof(f67,plain,(
% 11.76/2.00    ( ! [X4,X0,X1] : (v2_compts_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X4,X0) | ~r1_tarski(X4,k2_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.76/2.00    inference(equality_resolution,[],[f55])).
% 11.76/2.00  
% 11.76/2.00  fof(f53,plain,(
% 11.76/2.00    ( ! [X0] : (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 11.76/2.00    inference(cnf_transformation,[],[f31])).
% 11.76/2.00  
% 11.76/2.00  fof(f60,plain,(
% 11.76/2.00    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1) | ~sP0(X0,X1)) )),
% 11.76/2.00    inference(cnf_transformation,[],[f38])).
% 11.76/2.00  
% 11.76/2.00  fof(f65,plain,(
% 11.76/2.00    v1_compts_1(k1_pre_topc(sK2,sK3)) | v2_compts_1(sK3,sK2) | sP0(sK3,sK2)),
% 11.76/2.00    inference(cnf_transformation,[],[f43])).
% 11.76/2.00  
% 11.76/2.00  fof(f58,plain,(
% 11.76/2.00    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(sK1(X1,X2),X1) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.76/2.00    inference(cnf_transformation,[],[f35])).
% 11.76/2.00  
% 11.76/2.00  cnf(c_21,negated_conjecture,
% 11.76/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 11.76/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1212,plain,
% 11.76/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_4,plain,
% 11.76/2.00      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 11.76/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.76/2.00      | ~ l1_pre_topc(X0) ),
% 11.76/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1216,plain,
% 11.76/2.00      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 11.76/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.76/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1852,plain,
% 11.76/2.00      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top
% 11.76/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_1212,c_1216]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_22,negated_conjecture,
% 11.76/2.00      ( l1_pre_topc(sK2) ),
% 11.76/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_23,plain,
% 11.76/2.00      ( l1_pre_topc(sK2) = iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_24,plain,
% 11.76/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1404,plain,
% 11.76/2.00      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
% 11.76/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.76/2.00      | ~ l1_pre_topc(sK2) ),
% 11.76/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1405,plain,
% 11.76/2.00      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top
% 11.76/2.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.76/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_1404]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2058,plain,
% 11.76/2.00      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) = iProver_top ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_1852,c_23,c_24,c_1405]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_6,plain,
% 11.76/2.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 11.76/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1215,plain,
% 11.76/2.00      ( m1_pre_topc(X0,X1) != iProver_top
% 11.76/2.00      | l1_pre_topc(X1) != iProver_top
% 11.76/2.00      | l1_pre_topc(X0) = iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2063,plain,
% 11.76/2.00      ( l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top
% 11.76/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_2058,c_1215]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1449,plain,
% 11.76/2.00      ( ~ m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
% 11.76/2.00      | l1_pre_topc(k1_pre_topc(sK2,sK3))
% 11.76/2.00      | ~ l1_pre_topc(sK2) ),
% 11.76/2.00      inference(instantiation,[status(thm)],[c_6]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1450,plain,
% 11.76/2.00      ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 11.76/2.00      | l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top
% 11.76/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_1449]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2344,plain,
% 11.76/2.00      ( l1_pre_topc(k1_pre_topc(sK2,sK3)) = iProver_top ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_2063,c_23,c_24,c_1405,c_1450]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_5,plain,
% 11.76/2.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 11.76/2.00      inference(cnf_transformation,[],[f49]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_3,plain,
% 11.76/2.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.76/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_246,plain,
% 11.76/2.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.76/2.00      inference(resolution,[status(thm)],[c_5,c_3]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1210,plain,
% 11.76/2.00      ( u1_struct_0(X0) = k2_struct_0(X0) | l1_pre_topc(X0) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_246]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2862,plain,
% 11.76/2.00      ( u1_struct_0(k1_pre_topc(sK2,sK3)) = k2_struct_0(k1_pre_topc(sK2,sK3)) ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_2344,c_1210]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_7,plain,
% 11.76/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.76/2.00      | ~ l1_pre_topc(X1)
% 11.76/2.00      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 11.76/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1214,plain,
% 11.76/2.00      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
% 11.76/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.76/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1738,plain,
% 11.76/2.00      ( u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3
% 11.76/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_1212,c_1214]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1409,plain,
% 11.76/2.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.76/2.00      | ~ l1_pre_topc(sK2)
% 11.76/2.00      | u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
% 11.76/2.00      inference(instantiation,[status(thm)],[c_7]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2006,plain,
% 11.76/2.00      ( u1_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_1738,c_22,c_21,c_1409]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2864,plain,
% 11.76/2.00      ( k2_struct_0(k1_pre_topc(sK2,sK3)) = sK3 ),
% 11.76/2.00      inference(light_normalisation,[status(thm)],[c_2862,c_2006]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_8,plain,
% 11.76/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.76/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 11.76/2.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.76/2.00      | ~ l1_pre_topc(X1) ),
% 11.76/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1213,plain,
% 11.76/2.00      ( m1_pre_topc(X0,X1) != iProver_top
% 11.76/2.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.76/2.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.76/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1871,plain,
% 11.76/2.00      ( m1_pre_topc(sK2,X0) != iProver_top
% 11.76/2.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 11.76/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_1212,c_1213]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2,plain,
% 11.76/2.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.76/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_12,plain,
% 11.76/2.00      ( v2_compts_1(X0,X1)
% 11.76/2.00      | ~ m1_pre_topc(X2,X1)
% 11.76/2.00      | ~ r1_tarski(X0,k2_struct_0(X2))
% 11.76/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.76/2.00      | ~ l1_pre_topc(X1)
% 11.76/2.00      | sK1(X2,X0) = X0 ),
% 11.76/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_309,plain,
% 11.76/2.00      ( v2_compts_1(X0,X1)
% 11.76/2.00      | ~ m1_pre_topc(X2,X1)
% 11.76/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 11.76/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.76/2.00      | ~ l1_pre_topc(X1)
% 11.76/2.00      | X0 != X3
% 11.76/2.00      | sK1(X2,X0) = X0
% 11.76/2.00      | k2_struct_0(X2) != X4 ),
% 11.76/2.00      inference(resolution_lifted,[status(thm)],[c_2,c_12]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_310,plain,
% 11.76/2.00      ( v2_compts_1(X0,X1)
% 11.76/2.00      | ~ m1_pre_topc(X2,X1)
% 11.76/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.76/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X2)))
% 11.76/2.00      | ~ l1_pre_topc(X1)
% 11.76/2.00      | sK1(X2,X0) = X0 ),
% 11.76/2.00      inference(unflattening,[status(thm)],[c_309]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1207,plain,
% 11.76/2.00      ( sK1(X0,X1) = X1
% 11.76/2.00      | v2_compts_1(X1,X2) = iProver_top
% 11.76/2.00      | m1_pre_topc(X0,X2) != iProver_top
% 11.76/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 11.76/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(X0))) != iProver_top
% 11.76/2.00      | l1_pre_topc(X2) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2611,plain,
% 11.76/2.00      ( sK1(X0,sK3) = sK3
% 11.76/2.00      | v2_compts_1(sK3,X1) = iProver_top
% 11.76/2.00      | m1_pre_topc(X0,X1) != iProver_top
% 11.76/2.00      | m1_pre_topc(sK2,X1) != iProver_top
% 11.76/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(X0))) != iProver_top
% 11.76/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_1871,c_1207]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_5326,plain,
% 11.76/2.00      ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
% 11.76/2.00      | v2_compts_1(sK3,X0) = iProver_top
% 11.76/2.00      | m1_pre_topc(k1_pre_topc(sK2,sK3),X0) != iProver_top
% 11.76/2.00      | m1_pre_topc(sK2,X0) != iProver_top
% 11.76/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
% 11.76/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_2864,c_2611]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2609,plain,
% 11.76/2.00      ( sK1(X0,sK3) = sK3
% 11.76/2.00      | v2_compts_1(sK3,sK2) = iProver_top
% 11.76/2.00      | m1_pre_topc(X0,sK2) != iProver_top
% 11.76/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(X0))) != iProver_top
% 11.76/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_1212,c_1207]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_3217,plain,
% 11.76/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(X0))) != iProver_top
% 11.76/2.00      | m1_pre_topc(X0,sK2) != iProver_top
% 11.76/2.00      | v2_compts_1(sK3,sK2) = iProver_top
% 11.76/2.00      | sK1(X0,sK3) = sK3 ),
% 11.76/2.00      inference(global_propositional_subsumption,[status(thm)],[c_2609,c_23]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_3218,plain,
% 11.76/2.00      ( sK1(X0,sK3) = sK3
% 11.76/2.00      | v2_compts_1(sK3,sK2) = iProver_top
% 11.76/2.00      | m1_pre_topc(X0,sK2) != iProver_top
% 11.76/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(X0))) != iProver_top ),
% 11.76/2.00      inference(renaming,[status(thm)],[c_3217]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_3401,plain,
% 11.76/2.00      ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
% 11.76/2.00      | v2_compts_1(sK3,sK2) = iProver_top
% 11.76/2.00      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 11.76/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_2864,c_3218]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_5197,plain,
% 11.76/2.00      ( v2_compts_1(sK3,sK2) = iProver_top
% 11.76/2.00      | sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
% 11.76/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_3401,c_23,c_24,c_1405]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_5198,plain,
% 11.76/2.00      ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
% 11.76/2.00      | v2_compts_1(sK3,sK2) = iProver_top
% 11.76/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top ),
% 11.76/2.00      inference(renaming,[status(thm)],[c_5197]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1,plain,
% 11.76/2.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 11.76/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1217,plain,
% 11.76/2.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_0,plain,
% 11.76/2.00      ( k2_subset_1(X0) = X0 ),
% 11.76/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1224,plain,
% 11.76/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.76/2.00      inference(light_normalisation,[status(thm)],[c_1217,c_0]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_5204,plain,
% 11.76/2.00      ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3
% 11.76/2.00      | v2_compts_1(sK3,sK2) = iProver_top ),
% 11.76/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_5198,c_1224]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_9,plain,
% 11.76/2.00      ( ~ v2_compts_1(k2_struct_0(X0),X0)
% 11.76/2.00      | v1_compts_1(X0)
% 11.76/2.00      | ~ l1_pre_topc(X0) ),
% 11.76/2.00      inference(cnf_transformation,[],[f54]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_15,plain,
% 11.76/2.00      ( ~ sP0(X0,X1)
% 11.76/2.00      | ~ v2_compts_1(X0,X1)
% 11.76/2.00      | ~ v1_compts_1(k1_pre_topc(X1,X0)) ),
% 11.76/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_18,negated_conjecture,
% 11.76/2.00      ( sP0(sK3,sK2)
% 11.76/2.00      | ~ v2_compts_1(sK3,sK2)
% 11.76/2.00      | ~ v1_compts_1(k1_pre_topc(sK2,sK3)) ),
% 11.76/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_459,plain,
% 11.76/2.00      ( ~ v2_compts_1(X0,X1)
% 11.76/2.00      | ~ v2_compts_1(sK3,sK2)
% 11.76/2.00      | ~ v1_compts_1(k1_pre_topc(X1,X0))
% 11.76/2.00      | ~ v1_compts_1(k1_pre_topc(sK2,sK3))
% 11.76/2.00      | sK3 != X0
% 11.76/2.00      | sK2 != X1 ),
% 11.76/2.00      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_460,plain,
% 11.76/2.00      ( ~ v2_compts_1(sK3,sK2) | ~ v1_compts_1(k1_pre_topc(sK2,sK3)) ),
% 11.76/2.00      inference(unflattening,[status(thm)],[c_459]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_479,plain,
% 11.76/2.00      ( ~ v2_compts_1(k2_struct_0(X0),X0)
% 11.76/2.00      | ~ v2_compts_1(sK3,sK2)
% 11.76/2.00      | ~ l1_pre_topc(X0)
% 11.76/2.00      | k1_pre_topc(sK2,sK3) != X0 ),
% 11.76/2.00      inference(resolution_lifted,[status(thm)],[c_9,c_460]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_480,plain,
% 11.76/2.00      ( ~ v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3))
% 11.76/2.00      | ~ v2_compts_1(sK3,sK2)
% 11.76/2.00      | ~ l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
% 11.76/2.00      inference(unflattening,[status(thm)],[c_479]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1205,plain,
% 11.76/2.00      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) != iProver_top
% 11.76/2.00      | v2_compts_1(sK3,sK2) != iProver_top
% 11.76/2.00      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_3388,plain,
% 11.76/2.00      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
% 11.76/2.00      | v2_compts_1(sK3,sK2) != iProver_top
% 11.76/2.00      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 11.76/2.00      inference(demodulation,[status(thm)],[c_2864,c_1205]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_14072,plain,
% 11.76/2.00      ( v2_compts_1(sK3,sK2) != iProver_top
% 11.76/2.00      | v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_3388,c_23,c_24,c_1405,c_1450]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_14073,plain,
% 11.76/2.00      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
% 11.76/2.00      | v2_compts_1(sK3,sK2) != iProver_top ),
% 11.76/2.00      inference(renaming,[status(thm)],[c_14072]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_14,plain,
% 11.76/2.00      ( ~ v2_compts_1(X0,X1)
% 11.76/2.00      | v2_compts_1(X0,X2)
% 11.76/2.00      | ~ m1_pre_topc(X2,X1)
% 11.76/2.00      | ~ r1_tarski(X0,k2_struct_0(X2))
% 11.76/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 11.76/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.76/2.00      | ~ l1_pre_topc(X1) ),
% 11.76/2.00      inference(cnf_transformation,[],[f67]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_260,plain,
% 11.76/2.00      ( ~ v2_compts_1(X0,X1)
% 11.76/2.00      | v2_compts_1(X0,X2)
% 11.76/2.00      | ~ m1_pre_topc(X2,X1)
% 11.76/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 11.76/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 11.76/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.76/2.00      | ~ l1_pre_topc(X1)
% 11.76/2.00      | X0 != X3
% 11.76/2.00      | k2_struct_0(X2) != X4 ),
% 11.76/2.00      inference(resolution_lifted,[status(thm)],[c_2,c_14]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_261,plain,
% 11.76/2.00      ( ~ v2_compts_1(X0,X1)
% 11.76/2.00      | v2_compts_1(X0,X2)
% 11.76/2.00      | ~ m1_pre_topc(X2,X1)
% 11.76/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.76/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 11.76/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X2)))
% 11.76/2.00      | ~ l1_pre_topc(X1) ),
% 11.76/2.00      inference(unflattening,[status(thm)],[c_260]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_277,plain,
% 11.76/2.00      ( ~ v2_compts_1(X0,X1)
% 11.76/2.00      | v2_compts_1(X0,X2)
% 11.76/2.00      | ~ m1_pre_topc(X2,X1)
% 11.76/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 11.76/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X2)))
% 11.76/2.00      | ~ l1_pre_topc(X1) ),
% 11.76/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_261,c_8]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1209,plain,
% 11.76/2.00      ( v2_compts_1(X0,X1) != iProver_top
% 11.76/2.00      | v2_compts_1(X0,X2) = iProver_top
% 11.76/2.00      | m1_pre_topc(X2,X1) != iProver_top
% 11.76/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 11.76/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X2))) != iProver_top
% 11.76/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_277]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_5517,plain,
% 11.76/2.00      ( v2_compts_1(u1_struct_0(X0),X1) != iProver_top
% 11.76/2.00      | v2_compts_1(u1_struct_0(X0),X0) = iProver_top
% 11.76/2.00      | m1_pre_topc(X0,X1) != iProver_top
% 11.76/2.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(X0))) != iProver_top
% 11.76/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_1224,c_1209]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_18882,plain,
% 11.76/2.00      ( v2_compts_1(u1_struct_0(k1_pre_topc(sK2,sK3)),X0) != iProver_top
% 11.76/2.00      | v2_compts_1(u1_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
% 11.76/2.00      | m1_pre_topc(k1_pre_topc(sK2,sK3),X0) != iProver_top
% 11.76/2.00      | m1_subset_1(u1_struct_0(k1_pre_topc(sK2,sK3)),k1_zfmisc_1(sK3)) != iProver_top
% 11.76/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_2864,c_5517]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_18888,plain,
% 11.76/2.00      ( v2_compts_1(sK3,X0) != iProver_top
% 11.76/2.00      | v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
% 11.76/2.00      | m1_pre_topc(k1_pre_topc(sK2,sK3),X0) != iProver_top
% 11.76/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
% 11.76/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.76/2.00      inference(light_normalisation,[status(thm)],[c_18882,c_2006]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_10,plain,
% 11.76/2.00      ( v2_compts_1(k2_struct_0(X0),X0)
% 11.76/2.00      | ~ v1_compts_1(X0)
% 11.76/2.00      | ~ l1_pre_topc(X0) ),
% 11.76/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_16,plain,
% 11.76/2.00      ( ~ sP0(X0,X1) | v2_compts_1(X0,X1) | v1_compts_1(k1_pre_topc(X1,X0)) ),
% 11.76/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_19,negated_conjecture,
% 11.76/2.00      ( sP0(sK3,sK2)
% 11.76/2.00      | v2_compts_1(sK3,sK2)
% 11.76/2.00      | v1_compts_1(k1_pre_topc(sK2,sK3)) ),
% 11.76/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_432,plain,
% 11.76/2.00      ( v2_compts_1(X0,X1)
% 11.76/2.00      | v2_compts_1(sK3,sK2)
% 11.76/2.00      | v1_compts_1(k1_pre_topc(X1,X0))
% 11.76/2.00      | v1_compts_1(k1_pre_topc(sK2,sK3))
% 11.76/2.00      | sK3 != X0
% 11.76/2.00      | sK2 != X1 ),
% 11.76/2.00      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_433,plain,
% 11.76/2.00      ( v2_compts_1(sK3,sK2) | v1_compts_1(k1_pre_topc(sK2,sK3)) ),
% 11.76/2.00      inference(unflattening,[status(thm)],[c_432]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_492,plain,
% 11.76/2.00      ( v2_compts_1(k2_struct_0(X0),X0)
% 11.76/2.00      | v2_compts_1(sK3,sK2)
% 11.76/2.00      | ~ l1_pre_topc(X0)
% 11.76/2.00      | k1_pre_topc(sK2,sK3) != X0 ),
% 11.76/2.00      inference(resolution_lifted,[status(thm)],[c_10,c_433]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_493,plain,
% 11.76/2.00      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3))
% 11.76/2.00      | v2_compts_1(sK3,sK2)
% 11.76/2.00      | ~ l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
% 11.76/2.00      inference(unflattening,[status(thm)],[c_492]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1204,plain,
% 11.76/2.00      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
% 11.76/2.00      | v2_compts_1(sK3,sK2) = iProver_top
% 11.76/2.00      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_493]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_494,plain,
% 11.76/2.00      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
% 11.76/2.00      | v2_compts_1(sK3,sK2) = iProver_top
% 11.76/2.00      | l1_pre_topc(k1_pre_topc(sK2,sK3)) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_493]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1481,plain,
% 11.76/2.00      ( v2_compts_1(sK3,sK2) = iProver_top
% 11.76/2.00      | v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_1204,c_23,c_24,c_494,c_1405,c_1450]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1482,plain,
% 11.76/2.00      ( v2_compts_1(k2_struct_0(k1_pre_topc(sK2,sK3)),k1_pre_topc(sK2,sK3)) = iProver_top
% 11.76/2.00      | v2_compts_1(sK3,sK2) = iProver_top ),
% 11.76/2.00      inference(renaming,[status(thm)],[c_1481]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_3387,plain,
% 11.76/2.00      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
% 11.76/2.00      | v2_compts_1(sK3,sK2) = iProver_top ),
% 11.76/2.00      inference(demodulation,[status(thm)],[c_2864,c_1482]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_18952,plain,
% 11.76/2.00      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
% 11.76/2.00      | v2_compts_1(sK3,sK2) != iProver_top
% 11.76/2.00      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 11.76/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
% 11.76/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.76/2.00      inference(instantiation,[status(thm)],[c_18888]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_19149,plain,
% 11.76/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top
% 11.76/2.00      | v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_18888,c_23,c_24,c_1405,c_3387,c_18952]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_19150,plain,
% 11.76/2.00      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top
% 11.76/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top ),
% 11.76/2.00      inference(renaming,[status(thm)],[c_19149]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_19155,plain,
% 11.76/2.00      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) = iProver_top ),
% 11.76/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_19150,c_1224]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_42408,plain,
% 11.76/2.00      ( sK1(k1_pre_topc(sK2,sK3),sK3) = sK3 ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_5326,c_5204,c_14073,c_19155]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_11,plain,
% 11.76/2.00      ( v2_compts_1(X0,X1)
% 11.76/2.00      | ~ v2_compts_1(sK1(X2,X0),X2)
% 11.76/2.00      | ~ m1_pre_topc(X2,X1)
% 11.76/2.00      | ~ r1_tarski(X0,k2_struct_0(X2))
% 11.76/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.76/2.00      | ~ l1_pre_topc(X1) ),
% 11.76/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_333,plain,
% 11.76/2.00      ( v2_compts_1(X0,X1)
% 11.76/2.00      | ~ v2_compts_1(sK1(X2,X0),X2)
% 11.76/2.00      | ~ m1_pre_topc(X2,X1)
% 11.76/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 11.76/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.76/2.00      | ~ l1_pre_topc(X1)
% 11.76/2.00      | X0 != X3
% 11.76/2.00      | k2_struct_0(X2) != X4 ),
% 11.76/2.00      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_334,plain,
% 11.76/2.00      ( v2_compts_1(X0,X1)
% 11.76/2.00      | ~ v2_compts_1(sK1(X2,X0),X2)
% 11.76/2.00      | ~ m1_pre_topc(X2,X1)
% 11.76/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.76/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X2)))
% 11.76/2.00      | ~ l1_pre_topc(X1) ),
% 11.76/2.00      inference(unflattening,[status(thm)],[c_333]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1206,plain,
% 11.76/2.00      ( v2_compts_1(X0,X1) = iProver_top
% 11.76/2.00      | v2_compts_1(sK1(X2,X0),X2) != iProver_top
% 11.76/2.00      | m1_pre_topc(X2,X1) != iProver_top
% 11.76/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.76/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(X2))) != iProver_top
% 11.76/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.76/2.00      inference(predicate_to_equality,[status(thm)],[c_334]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_1620,plain,
% 11.76/2.00      ( v2_compts_1(sK1(X0,sK3),X0) != iProver_top
% 11.76/2.00      | v2_compts_1(sK3,sK2) = iProver_top
% 11.76/2.00      | m1_pre_topc(X0,sK2) != iProver_top
% 11.76/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(X0))) != iProver_top
% 11.76/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_1212,c_1206]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2236,plain,
% 11.76/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(X0))) != iProver_top
% 11.76/2.00      | m1_pre_topc(X0,sK2) != iProver_top
% 11.76/2.00      | v2_compts_1(sK3,sK2) = iProver_top
% 11.76/2.00      | v2_compts_1(sK1(X0,sK3),X0) != iProver_top ),
% 11.76/2.00      inference(global_propositional_subsumption,[status(thm)],[c_1620,c_23]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_2237,plain,
% 11.76/2.00      ( v2_compts_1(sK1(X0,sK3),X0) != iProver_top
% 11.76/2.00      | v2_compts_1(sK3,sK2) = iProver_top
% 11.76/2.00      | m1_pre_topc(X0,sK2) != iProver_top
% 11.76/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(X0))) != iProver_top ),
% 11.76/2.00      inference(renaming,[status(thm)],[c_2236]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_42413,plain,
% 11.76/2.00      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
% 11.76/2.00      | v2_compts_1(sK3,sK2) = iProver_top
% 11.76/2.00      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 11.76/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(k1_pre_topc(sK2,sK3)))) != iProver_top ),
% 11.76/2.00      inference(superposition,[status(thm)],[c_42408,c_2237]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_42448,plain,
% 11.76/2.00      ( v2_compts_1(sK3,k1_pre_topc(sK2,sK3)) != iProver_top
% 11.76/2.00      | v2_compts_1(sK3,sK2) = iProver_top
% 11.76/2.00      | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) != iProver_top
% 11.76/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top ),
% 11.76/2.00      inference(light_normalisation,[status(thm)],[c_42413,c_2864]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_44484,plain,
% 11.76/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top ),
% 11.76/2.00      inference(global_propositional_subsumption,
% 11.76/2.00                [status(thm)],
% 11.76/2.00                [c_42448,c_23,c_24,c_1405,c_14073,c_19155]) ).
% 11.76/2.00  
% 11.76/2.00  cnf(c_44489,plain,
% 11.76/2.00      ( $false ),
% 11.76/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_44484,c_1224]) ).
% 11.76/2.00  
% 11.76/2.00  
% 11.76/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.76/2.00  
% 11.76/2.00  ------                               Statistics
% 11.76/2.00  
% 11.76/2.00  ------ Selected
% 11.76/2.00  
% 11.76/2.00  total_time:                             1.251
% 11.76/2.00  
%------------------------------------------------------------------------------
