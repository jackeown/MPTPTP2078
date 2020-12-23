%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:44 EST 2020

% Result     : Theorem 4.05s
% Output     : CNFRefutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :  186 (1218 expanded)
%              Number of clauses        :  116 ( 355 expanded)
%              Number of leaves         :   19 ( 294 expanded)
%              Depth                    :   24
%              Number of atoms          :  788 (10749 expanded)
%              Number of equality atoms :  269 (1315 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f53,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
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

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

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

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                 => ( ( m1_pre_topc(X1,X0)
                      & v1_tsep_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,X0)
            | ~ v1_tsep_1(X2,X0)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( ( m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0) )
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
     => ( ( ~ m1_pre_topc(sK2,X0)
          | ~ v1_tsep_1(sK2,X0)
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
        & ( ( m1_pre_topc(sK2,X0)
            & v1_tsep_1(sK2,X0) )
          | ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) ) )
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = sK2
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | ~ m1_pre_topc(sK1,X0)
              | ~ v1_tsep_1(sK1,X0) )
            & ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0) )
              | ( m1_pre_topc(sK1,X0)
                & v1_tsep_1(sK1,X0) ) )
            & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) ) )
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK0)
                | ~ v1_tsep_1(X2,sK0)
                | ~ m1_pre_topc(X1,sK0)
                | ~ v1_tsep_1(X1,sK0) )
              & ( ( m1_pre_topc(X2,sK0)
                  & v1_tsep_1(X2,sK0) )
                | ( m1_pre_topc(X1,sK0)
                  & v1_tsep_1(X1,sK0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ~ m1_pre_topc(sK2,sK0)
      | ~ v1_tsep_1(sK2,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_tsep_1(sK1,sK0) )
    & ( ( m1_pre_topc(sK2,sK0)
        & v1_tsep_1(sK2,sK0) )
      | ( m1_pre_topc(sK1,sK0)
        & v1_tsep_1(sK1,sK0) ) )
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f40,f39,f38])).

fof(f64,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f70,plain,
    ( m1_pre_topc(sK2,sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f72,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,
    ( v1_tsep_1(sK2,sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_11,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1249,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1256,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1255,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1238,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_384,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_6,c_5])).

cnf(c_1232,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_1536,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1238,c_1232])).

cnf(c_9,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1251,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2560,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1536,c_1251])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1240,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1535,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_1240,c_1232])).

cnf(c_24,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1713,plain,
    ( g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(demodulation,[status(thm)],[c_1536,c_24])).

cnf(c_2566,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2560,c_1535,c_1536,c_1713])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_33,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_34,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2872,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2566,c_33,c_34])).

cnf(c_2878,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
    | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1255,c_2872])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1254,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4862,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2878,c_1254])).

cnf(c_6701,plain,
    ( v3_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_4862])).

cnf(c_7,plain,
    ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1253,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2694,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1536,c_1253])).

cnf(c_2699,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2694,c_1535,c_1536,c_1713])).

cnf(c_2940,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2699,c_33,c_34])).

cnf(c_2946,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | r1_tarski(X0,k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1255,c_2940])).

cnf(c_4934,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK1)) = iProver_top
    | r1_tarski(X0,k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2946,c_1254])).

cnf(c_7268,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_4934])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_35,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_36,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7092,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_7093,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7092])).

cnf(c_7275,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7268,c_35,c_36,c_7093])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1257,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7279,plain,
    ( k2_struct_0(sK1) = k2_struct_0(sK2)
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7275,c_1257])).

cnf(c_7350,plain,
    ( k2_struct_0(sK1) = k2_struct_0(sK2)
    | v3_pre_topc(k2_struct_0(sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6701,c_7279])).

cnf(c_13273,plain,
    ( k2_struct_0(sK1) = k2_struct_0(sK2)
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_7350])).

cnf(c_13352,plain,
    ( k2_struct_0(sK1) = k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13273,c_33,c_34])).

cnf(c_16,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_175,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_18])).

cnf(c_176,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_175])).

cnf(c_1233,plain,
    ( v1_tsep_1(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_176])).

cnf(c_1847,plain,
    ( v1_tsep_1(sK1,X0) = iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | v3_pre_topc(k2_struct_0(sK1),X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1536,c_1233])).

cnf(c_13397,plain,
    ( v1_tsep_1(sK1,X0) = iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | v3_pre_topc(k2_struct_0(sK2),X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13352,c_1847])).

cnf(c_13458,plain,
    ( v1_tsep_1(sK1,sK0) = iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v3_pre_topc(k2_struct_0(sK2),sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13397])).

cnf(c_17,plain,
    ( ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_168,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_18])).

cnf(c_169,plain,
    ( ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_168])).

cnf(c_1234,plain,
    ( v1_tsep_1(X0,X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_169])).

cnf(c_2454,plain,
    ( v1_tsep_1(sK1,X0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | v3_pre_topc(k2_struct_0(sK1),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1536,c_1234])).

cnf(c_13384,plain,
    ( v1_tsep_1(sK1,X0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | v3_pre_topc(k2_struct_0(sK2),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13352,c_2454])).

cnf(c_13451,plain,
    ( v1_tsep_1(sK1,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v3_pre_topc(k2_struct_0(sK2),sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13384])).

cnf(c_2456,plain,
    ( v1_tsep_1(sK2,X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | v3_pre_topc(k2_struct_0(sK2),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1234])).

cnf(c_2465,plain,
    ( v1_tsep_1(sK2,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v3_pre_topc(k2_struct_0(sK2),sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2456])).

cnf(c_633,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1886,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != X0 ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_2315,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1886])).

cnf(c_2316,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2315])).

cnf(c_638,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1660,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK2,sK0)
    | X1 != sK0
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_1923,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
    | ~ m1_pre_topc(sK2,sK0)
    | X0 != sK0
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1660])).

cnf(c_1924,plain,
    ( X0 != sK0
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1923])).

cnf(c_1926,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
    | sK0 != sK0
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1924])).

cnf(c_1849,plain,
    ( v1_tsep_1(sK2,X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | v3_pre_topc(k2_struct_0(sK2),X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1233])).

cnf(c_1857,plain,
    ( v1_tsep_1(sK2,sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v3_pre_topc(k2_struct_0(sK2),sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1849])).

cnf(c_21,negated_conjecture,
    ( v1_tsep_1(sK1,sK0)
    | m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1243,plain,
    ( v1_tsep_1(sK1,sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_32,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK1,sK0)
    | m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_40,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_89,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_93,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_628,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1384,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_628])).

cnf(c_629,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1337,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_1393,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1337])).

cnf(c_1469,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
    | sK2 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1393])).

cnf(c_1307,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(sK2,sK0)
    | sK0 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_1505,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
    | m1_pre_topc(sK2,sK0)
    | sK0 != X0
    | sK2 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(instantiation,[status(thm)],[c_1307])).

cnf(c_1506,plain,
    ( sK0 != X0
    | sK2 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1505])).

cnf(c_1508,plain,
    ( sK0 != sK0
    | sK2 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1568,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1569,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) = iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_1675,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1243,c_32,c_24,c_40,c_89,c_93,c_1384,c_1469,c_1508,c_1569])).

cnf(c_14,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1651,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
    | m1_pre_topc(sK1,X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1652,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(sK1,X0) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1651])).

cnf(c_1654,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_637,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1415,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X0 ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_1574,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1415])).

cnf(c_1575,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1574])).

cnf(c_19,negated_conjecture,
    ( ~ v1_tsep_1(sK1,sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_41,plain,
    ( v1_tsep_1(sK1,sK0) != iProver_top
    | v1_tsep_1(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_23,negated_conjecture,
    ( v1_tsep_1(sK1,sK0)
    | v1_tsep_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_37,plain,
    ( v1_tsep_1(sK1,sK0) = iProver_top
    | v1_tsep_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_31,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13458,c_13451,c_2465,c_2316,c_1926,c_1857,c_1675,c_1654,c_1575,c_93,c_89,c_41,c_37,c_24,c_36,c_35,c_34,c_33,c_32,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n009.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 09:34:41 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 4.05/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.05/0.98  
% 4.05/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.05/0.98  
% 4.05/0.98  ------  iProver source info
% 4.05/0.98  
% 4.05/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.05/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.05/0.98  git: non_committed_changes: false
% 4.05/0.98  git: last_make_outside_of_git: false
% 4.05/0.98  
% 4.05/0.98  ------ 
% 4.05/0.98  
% 4.05/0.98  ------ Input Options
% 4.05/0.98  
% 4.05/0.98  --out_options                           all
% 4.05/0.98  --tptp_safe_out                         true
% 4.05/0.98  --problem_path                          ""
% 4.05/0.98  --include_path                          ""
% 4.05/0.98  --clausifier                            res/vclausify_rel
% 4.05/0.98  --clausifier_options                    ""
% 4.05/0.98  --stdin                                 false
% 4.05/0.98  --stats_out                             all
% 4.05/0.98  
% 4.05/0.98  ------ General Options
% 4.05/0.98  
% 4.05/0.98  --fof                                   false
% 4.05/0.98  --time_out_real                         305.
% 4.05/0.98  --time_out_virtual                      -1.
% 4.05/0.98  --symbol_type_check                     false
% 4.05/0.98  --clausify_out                          false
% 4.05/0.98  --sig_cnt_out                           false
% 4.05/0.98  --trig_cnt_out                          false
% 4.05/0.98  --trig_cnt_out_tolerance                1.
% 4.05/0.98  --trig_cnt_out_sk_spl                   false
% 4.05/0.98  --abstr_cl_out                          false
% 4.05/0.98  
% 4.05/0.98  ------ Global Options
% 4.05/0.98  
% 4.05/0.98  --schedule                              default
% 4.05/0.98  --add_important_lit                     false
% 4.05/0.98  --prop_solver_per_cl                    1000
% 4.05/0.98  --min_unsat_core                        false
% 4.05/0.98  --soft_assumptions                      false
% 4.05/0.98  --soft_lemma_size                       3
% 4.05/0.98  --prop_impl_unit_size                   0
% 4.05/0.98  --prop_impl_unit                        []
% 4.05/0.98  --share_sel_clauses                     true
% 4.05/0.98  --reset_solvers                         false
% 4.05/0.98  --bc_imp_inh                            [conj_cone]
% 4.05/0.98  --conj_cone_tolerance                   3.
% 4.05/0.98  --extra_neg_conj                        none
% 4.05/0.98  --large_theory_mode                     true
% 4.05/0.98  --prolific_symb_bound                   200
% 4.05/0.98  --lt_threshold                          2000
% 4.05/0.98  --clause_weak_htbl                      true
% 4.05/0.98  --gc_record_bc_elim                     false
% 4.05/0.98  
% 4.05/0.98  ------ Preprocessing Options
% 4.05/0.98  
% 4.05/0.98  --preprocessing_flag                    true
% 4.05/0.98  --time_out_prep_mult                    0.1
% 4.05/0.98  --splitting_mode                        input
% 4.05/0.98  --splitting_grd                         true
% 4.05/0.98  --splitting_cvd                         false
% 4.05/0.98  --splitting_cvd_svl                     false
% 4.05/0.98  --splitting_nvd                         32
% 4.05/0.98  --sub_typing                            true
% 4.05/0.98  --prep_gs_sim                           true
% 4.05/0.98  --prep_unflatten                        true
% 4.05/0.98  --prep_res_sim                          true
% 4.05/0.98  --prep_upred                            true
% 4.05/0.98  --prep_sem_filter                       exhaustive
% 4.05/0.98  --prep_sem_filter_out                   false
% 4.05/0.98  --pred_elim                             true
% 4.05/0.98  --res_sim_input                         true
% 4.05/0.98  --eq_ax_congr_red                       true
% 4.05/0.98  --pure_diseq_elim                       true
% 4.05/0.98  --brand_transform                       false
% 4.05/0.98  --non_eq_to_eq                          false
% 4.05/0.98  --prep_def_merge                        true
% 4.05/0.98  --prep_def_merge_prop_impl              false
% 4.05/0.98  --prep_def_merge_mbd                    true
% 4.05/0.98  --prep_def_merge_tr_red                 false
% 4.05/0.98  --prep_def_merge_tr_cl                  false
% 4.05/0.98  --smt_preprocessing                     true
% 4.05/0.98  --smt_ac_axioms                         fast
% 4.05/0.98  --preprocessed_out                      false
% 4.05/0.98  --preprocessed_stats                    false
% 4.05/0.98  
% 4.05/0.98  ------ Abstraction refinement Options
% 4.05/0.98  
% 4.05/0.98  --abstr_ref                             []
% 4.05/0.98  --abstr_ref_prep                        false
% 4.05/0.98  --abstr_ref_until_sat                   false
% 4.05/0.98  --abstr_ref_sig_restrict                funpre
% 4.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/0.98  --abstr_ref_under                       []
% 4.05/0.98  
% 4.05/0.98  ------ SAT Options
% 4.05/0.98  
% 4.05/0.98  --sat_mode                              false
% 4.05/0.98  --sat_fm_restart_options                ""
% 4.05/0.98  --sat_gr_def                            false
% 4.05/0.98  --sat_epr_types                         true
% 4.05/0.98  --sat_non_cyclic_types                  false
% 4.05/0.98  --sat_finite_models                     false
% 4.05/0.98  --sat_fm_lemmas                         false
% 4.05/0.98  --sat_fm_prep                           false
% 4.05/0.98  --sat_fm_uc_incr                        true
% 4.05/0.98  --sat_out_model                         small
% 4.05/0.98  --sat_out_clauses                       false
% 4.05/0.98  
% 4.05/0.98  ------ QBF Options
% 4.05/0.98  
% 4.05/0.98  --qbf_mode                              false
% 4.05/0.98  --qbf_elim_univ                         false
% 4.05/0.98  --qbf_dom_inst                          none
% 4.05/0.98  --qbf_dom_pre_inst                      false
% 4.05/0.98  --qbf_sk_in                             false
% 4.05/0.98  --qbf_pred_elim                         true
% 4.05/0.98  --qbf_split                             512
% 4.05/0.98  
% 4.05/0.98  ------ BMC1 Options
% 4.05/0.98  
% 4.05/0.98  --bmc1_incremental                      false
% 4.05/0.98  --bmc1_axioms                           reachable_all
% 4.05/0.98  --bmc1_min_bound                        0
% 4.05/0.98  --bmc1_max_bound                        -1
% 4.05/0.98  --bmc1_max_bound_default                -1
% 4.05/0.98  --bmc1_symbol_reachability              true
% 4.05/0.98  --bmc1_property_lemmas                  false
% 4.05/0.98  --bmc1_k_induction                      false
% 4.05/0.98  --bmc1_non_equiv_states                 false
% 4.05/0.98  --bmc1_deadlock                         false
% 4.05/0.98  --bmc1_ucm                              false
% 4.05/0.98  --bmc1_add_unsat_core                   none
% 4.05/0.98  --bmc1_unsat_core_children              false
% 4.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/0.98  --bmc1_out_stat                         full
% 4.05/0.98  --bmc1_ground_init                      false
% 4.05/0.98  --bmc1_pre_inst_next_state              false
% 4.05/0.98  --bmc1_pre_inst_state                   false
% 4.05/0.98  --bmc1_pre_inst_reach_state             false
% 4.05/0.98  --bmc1_out_unsat_core                   false
% 4.05/0.98  --bmc1_aig_witness_out                  false
% 4.05/0.98  --bmc1_verbose                          false
% 4.05/0.98  --bmc1_dump_clauses_tptp                false
% 4.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.05/0.98  --bmc1_dump_file                        -
% 4.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.05/0.98  --bmc1_ucm_extend_mode                  1
% 4.05/0.98  --bmc1_ucm_init_mode                    2
% 4.05/0.98  --bmc1_ucm_cone_mode                    none
% 4.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.05/0.98  --bmc1_ucm_relax_model                  4
% 4.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/0.98  --bmc1_ucm_layered_model                none
% 4.05/0.98  --bmc1_ucm_max_lemma_size               10
% 4.05/0.98  
% 4.05/0.98  ------ AIG Options
% 4.05/0.98  
% 4.05/0.98  --aig_mode                              false
% 4.05/0.98  
% 4.05/0.98  ------ Instantiation Options
% 4.05/0.98  
% 4.05/0.98  --instantiation_flag                    true
% 4.05/0.98  --inst_sos_flag                         true
% 4.05/0.98  --inst_sos_phase                        true
% 4.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/0.98  --inst_lit_sel_side                     num_symb
% 4.05/0.98  --inst_solver_per_active                1400
% 4.05/0.98  --inst_solver_calls_frac                1.
% 4.05/0.98  --inst_passive_queue_type               priority_queues
% 4.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/0.98  --inst_passive_queues_freq              [25;2]
% 4.05/0.98  --inst_dismatching                      true
% 4.05/0.98  --inst_eager_unprocessed_to_passive     true
% 4.05/0.98  --inst_prop_sim_given                   true
% 4.05/0.98  --inst_prop_sim_new                     false
% 4.05/0.98  --inst_subs_new                         false
% 4.05/0.98  --inst_eq_res_simp                      false
% 4.05/0.98  --inst_subs_given                       false
% 4.05/0.98  --inst_orphan_elimination               true
% 4.05/0.98  --inst_learning_loop_flag               true
% 4.05/0.98  --inst_learning_start                   3000
% 4.05/0.98  --inst_learning_factor                  2
% 4.05/0.98  --inst_start_prop_sim_after_learn       3
% 4.05/0.98  --inst_sel_renew                        solver
% 4.05/0.98  --inst_lit_activity_flag                true
% 4.05/0.98  --inst_restr_to_given                   false
% 4.05/0.98  --inst_activity_threshold               500
% 4.05/0.98  --inst_out_proof                        true
% 4.05/0.98  
% 4.05/0.98  ------ Resolution Options
% 4.05/0.98  
% 4.05/0.98  --resolution_flag                       true
% 4.05/0.98  --res_lit_sel                           adaptive
% 4.05/0.98  --res_lit_sel_side                      none
% 4.05/0.98  --res_ordering                          kbo
% 4.05/0.98  --res_to_prop_solver                    active
% 4.05/0.98  --res_prop_simpl_new                    false
% 4.05/0.98  --res_prop_simpl_given                  true
% 4.05/0.98  --res_passive_queue_type                priority_queues
% 4.05/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/0.99  --res_passive_queues_freq               [15;5]
% 4.05/0.99  --res_forward_subs                      full
% 4.05/0.99  --res_backward_subs                     full
% 4.05/0.99  --res_forward_subs_resolution           true
% 4.05/0.99  --res_backward_subs_resolution          true
% 4.05/0.99  --res_orphan_elimination                true
% 4.05/0.99  --res_time_limit                        2.
% 4.05/0.99  --res_out_proof                         true
% 4.05/0.99  
% 4.05/0.99  ------ Superposition Options
% 4.05/0.99  
% 4.05/0.99  --superposition_flag                    true
% 4.05/0.99  --sup_passive_queue_type                priority_queues
% 4.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.05/0.99  --demod_completeness_check              fast
% 4.05/0.99  --demod_use_ground                      true
% 4.05/0.99  --sup_to_prop_solver                    passive
% 4.05/0.99  --sup_prop_simpl_new                    true
% 4.05/0.99  --sup_prop_simpl_given                  true
% 4.05/0.99  --sup_fun_splitting                     true
% 4.05/0.99  --sup_smt_interval                      50000
% 4.05/0.99  
% 4.05/0.99  ------ Superposition Simplification Setup
% 4.05/0.99  
% 4.05/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.05/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.05/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.05/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.05/0.99  --sup_immed_triv                        [TrivRules]
% 4.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_immed_bw_main                     []
% 4.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_input_bw                          []
% 4.05/0.99  
% 4.05/0.99  ------ Combination Options
% 4.05/0.99  
% 4.05/0.99  --comb_res_mult                         3
% 4.05/0.99  --comb_sup_mult                         2
% 4.05/0.99  --comb_inst_mult                        10
% 4.05/0.99  
% 4.05/0.99  ------ Debug Options
% 4.05/0.99  
% 4.05/0.99  --dbg_backtrace                         false
% 4.05/0.99  --dbg_dump_prop_clauses                 false
% 4.05/0.99  --dbg_dump_prop_clauses_file            -
% 4.05/0.99  --dbg_out_stat                          false
% 4.05/0.99  ------ Parsing...
% 4.05/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.05/0.99  ------ Proving...
% 4.05/0.99  ------ Problem Properties 
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  clauses                                 27
% 4.05/0.99  conjectures                             12
% 4.05/0.99  EPR                                     13
% 4.05/0.99  Horn                                    23
% 4.05/0.99  unary                                   8
% 4.05/0.99  binary                                  7
% 4.05/0.99  lits                                    75
% 4.05/0.99  lits eq                                 3
% 4.05/0.99  fd_pure                                 0
% 4.05/0.99  fd_pseudo                               0
% 4.05/0.99  fd_cond                                 0
% 4.05/0.99  fd_pseudo_cond                          1
% 4.05/0.99  AC symbols                              0
% 4.05/0.99  
% 4.05/0.99  ------ Schedule dynamic 5 is on 
% 4.05/0.99  
% 4.05/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  ------ 
% 4.05/0.99  Current options:
% 4.05/0.99  ------ 
% 4.05/0.99  
% 4.05/0.99  ------ Input Options
% 4.05/0.99  
% 4.05/0.99  --out_options                           all
% 4.05/0.99  --tptp_safe_out                         true
% 4.05/0.99  --problem_path                          ""
% 4.05/0.99  --include_path                          ""
% 4.05/0.99  --clausifier                            res/vclausify_rel
% 4.05/0.99  --clausifier_options                    ""
% 4.05/0.99  --stdin                                 false
% 4.05/0.99  --stats_out                             all
% 4.05/0.99  
% 4.05/0.99  ------ General Options
% 4.05/0.99  
% 4.05/0.99  --fof                                   false
% 4.05/0.99  --time_out_real                         305.
% 4.05/0.99  --time_out_virtual                      -1.
% 4.05/0.99  --symbol_type_check                     false
% 4.05/0.99  --clausify_out                          false
% 4.05/0.99  --sig_cnt_out                           false
% 4.05/0.99  --trig_cnt_out                          false
% 4.05/0.99  --trig_cnt_out_tolerance                1.
% 4.05/0.99  --trig_cnt_out_sk_spl                   false
% 4.05/0.99  --abstr_cl_out                          false
% 4.05/0.99  
% 4.05/0.99  ------ Global Options
% 4.05/0.99  
% 4.05/0.99  --schedule                              default
% 4.05/0.99  --add_important_lit                     false
% 4.05/0.99  --prop_solver_per_cl                    1000
% 4.05/0.99  --min_unsat_core                        false
% 4.05/0.99  --soft_assumptions                      false
% 4.05/0.99  --soft_lemma_size                       3
% 4.05/0.99  --prop_impl_unit_size                   0
% 4.05/0.99  --prop_impl_unit                        []
% 4.05/0.99  --share_sel_clauses                     true
% 4.05/0.99  --reset_solvers                         false
% 4.05/0.99  --bc_imp_inh                            [conj_cone]
% 4.05/0.99  --conj_cone_tolerance                   3.
% 4.05/0.99  --extra_neg_conj                        none
% 4.05/0.99  --large_theory_mode                     true
% 4.05/0.99  --prolific_symb_bound                   200
% 4.05/0.99  --lt_threshold                          2000
% 4.05/0.99  --clause_weak_htbl                      true
% 4.05/0.99  --gc_record_bc_elim                     false
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing Options
% 4.05/0.99  
% 4.05/0.99  --preprocessing_flag                    true
% 4.05/0.99  --time_out_prep_mult                    0.1
% 4.05/0.99  --splitting_mode                        input
% 4.05/0.99  --splitting_grd                         true
% 4.05/0.99  --splitting_cvd                         false
% 4.05/0.99  --splitting_cvd_svl                     false
% 4.05/0.99  --splitting_nvd                         32
% 4.05/0.99  --sub_typing                            true
% 4.05/0.99  --prep_gs_sim                           true
% 4.05/0.99  --prep_unflatten                        true
% 4.05/0.99  --prep_res_sim                          true
% 4.05/0.99  --prep_upred                            true
% 4.05/0.99  --prep_sem_filter                       exhaustive
% 4.05/0.99  --prep_sem_filter_out                   false
% 4.05/0.99  --pred_elim                             true
% 4.05/0.99  --res_sim_input                         true
% 4.05/0.99  --eq_ax_congr_red                       true
% 4.05/0.99  --pure_diseq_elim                       true
% 4.05/0.99  --brand_transform                       false
% 4.05/0.99  --non_eq_to_eq                          false
% 4.05/0.99  --prep_def_merge                        true
% 4.05/0.99  --prep_def_merge_prop_impl              false
% 4.05/0.99  --prep_def_merge_mbd                    true
% 4.05/0.99  --prep_def_merge_tr_red                 false
% 4.05/0.99  --prep_def_merge_tr_cl                  false
% 4.05/0.99  --smt_preprocessing                     true
% 4.05/0.99  --smt_ac_axioms                         fast
% 4.05/0.99  --preprocessed_out                      false
% 4.05/0.99  --preprocessed_stats                    false
% 4.05/0.99  
% 4.05/0.99  ------ Abstraction refinement Options
% 4.05/0.99  
% 4.05/0.99  --abstr_ref                             []
% 4.05/0.99  --abstr_ref_prep                        false
% 4.05/0.99  --abstr_ref_until_sat                   false
% 4.05/0.99  --abstr_ref_sig_restrict                funpre
% 4.05/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/0.99  --abstr_ref_under                       []
% 4.05/0.99  
% 4.05/0.99  ------ SAT Options
% 4.05/0.99  
% 4.05/0.99  --sat_mode                              false
% 4.05/0.99  --sat_fm_restart_options                ""
% 4.05/0.99  --sat_gr_def                            false
% 4.05/0.99  --sat_epr_types                         true
% 4.05/0.99  --sat_non_cyclic_types                  false
% 4.05/0.99  --sat_finite_models                     false
% 4.05/0.99  --sat_fm_lemmas                         false
% 4.05/0.99  --sat_fm_prep                           false
% 4.05/0.99  --sat_fm_uc_incr                        true
% 4.05/0.99  --sat_out_model                         small
% 4.05/0.99  --sat_out_clauses                       false
% 4.05/0.99  
% 4.05/0.99  ------ QBF Options
% 4.05/0.99  
% 4.05/0.99  --qbf_mode                              false
% 4.05/0.99  --qbf_elim_univ                         false
% 4.05/0.99  --qbf_dom_inst                          none
% 4.05/0.99  --qbf_dom_pre_inst                      false
% 4.05/0.99  --qbf_sk_in                             false
% 4.05/0.99  --qbf_pred_elim                         true
% 4.05/0.99  --qbf_split                             512
% 4.05/0.99  
% 4.05/0.99  ------ BMC1 Options
% 4.05/0.99  
% 4.05/0.99  --bmc1_incremental                      false
% 4.05/0.99  --bmc1_axioms                           reachable_all
% 4.05/0.99  --bmc1_min_bound                        0
% 4.05/0.99  --bmc1_max_bound                        -1
% 4.05/0.99  --bmc1_max_bound_default                -1
% 4.05/0.99  --bmc1_symbol_reachability              true
% 4.05/0.99  --bmc1_property_lemmas                  false
% 4.05/0.99  --bmc1_k_induction                      false
% 4.05/0.99  --bmc1_non_equiv_states                 false
% 4.05/0.99  --bmc1_deadlock                         false
% 4.05/0.99  --bmc1_ucm                              false
% 4.05/0.99  --bmc1_add_unsat_core                   none
% 4.05/0.99  --bmc1_unsat_core_children              false
% 4.05/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/0.99  --bmc1_out_stat                         full
% 4.05/0.99  --bmc1_ground_init                      false
% 4.05/0.99  --bmc1_pre_inst_next_state              false
% 4.05/0.99  --bmc1_pre_inst_state                   false
% 4.05/0.99  --bmc1_pre_inst_reach_state             false
% 4.05/0.99  --bmc1_out_unsat_core                   false
% 4.05/0.99  --bmc1_aig_witness_out                  false
% 4.05/0.99  --bmc1_verbose                          false
% 4.05/0.99  --bmc1_dump_clauses_tptp                false
% 4.05/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.05/0.99  --bmc1_dump_file                        -
% 4.05/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.05/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.05/0.99  --bmc1_ucm_extend_mode                  1
% 4.05/0.99  --bmc1_ucm_init_mode                    2
% 4.05/0.99  --bmc1_ucm_cone_mode                    none
% 4.05/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.05/0.99  --bmc1_ucm_relax_model                  4
% 4.05/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.05/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/0.99  --bmc1_ucm_layered_model                none
% 4.05/0.99  --bmc1_ucm_max_lemma_size               10
% 4.05/0.99  
% 4.05/0.99  ------ AIG Options
% 4.05/0.99  
% 4.05/0.99  --aig_mode                              false
% 4.05/0.99  
% 4.05/0.99  ------ Instantiation Options
% 4.05/0.99  
% 4.05/0.99  --instantiation_flag                    true
% 4.05/0.99  --inst_sos_flag                         true
% 4.05/0.99  --inst_sos_phase                        true
% 4.05/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/0.99  --inst_lit_sel_side                     none
% 4.05/0.99  --inst_solver_per_active                1400
% 4.05/0.99  --inst_solver_calls_frac                1.
% 4.05/0.99  --inst_passive_queue_type               priority_queues
% 4.05/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/0.99  --inst_passive_queues_freq              [25;2]
% 4.05/0.99  --inst_dismatching                      true
% 4.05/0.99  --inst_eager_unprocessed_to_passive     true
% 4.05/0.99  --inst_prop_sim_given                   true
% 4.05/0.99  --inst_prop_sim_new                     false
% 4.05/0.99  --inst_subs_new                         false
% 4.05/0.99  --inst_eq_res_simp                      false
% 4.05/0.99  --inst_subs_given                       false
% 4.05/0.99  --inst_orphan_elimination               true
% 4.05/0.99  --inst_learning_loop_flag               true
% 4.05/0.99  --inst_learning_start                   3000
% 4.05/0.99  --inst_learning_factor                  2
% 4.05/0.99  --inst_start_prop_sim_after_learn       3
% 4.05/0.99  --inst_sel_renew                        solver
% 4.05/0.99  --inst_lit_activity_flag                true
% 4.05/0.99  --inst_restr_to_given                   false
% 4.05/0.99  --inst_activity_threshold               500
% 4.05/0.99  --inst_out_proof                        true
% 4.05/0.99  
% 4.05/0.99  ------ Resolution Options
% 4.05/0.99  
% 4.05/0.99  --resolution_flag                       false
% 4.05/0.99  --res_lit_sel                           adaptive
% 4.05/0.99  --res_lit_sel_side                      none
% 4.05/0.99  --res_ordering                          kbo
% 4.05/0.99  --res_to_prop_solver                    active
% 4.05/0.99  --res_prop_simpl_new                    false
% 4.05/0.99  --res_prop_simpl_given                  true
% 4.05/0.99  --res_passive_queue_type                priority_queues
% 4.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/0.99  --res_passive_queues_freq               [15;5]
% 4.05/0.99  --res_forward_subs                      full
% 4.05/0.99  --res_backward_subs                     full
% 4.05/0.99  --res_forward_subs_resolution           true
% 4.05/0.99  --res_backward_subs_resolution          true
% 4.05/0.99  --res_orphan_elimination                true
% 4.05/0.99  --res_time_limit                        2.
% 4.05/0.99  --res_out_proof                         true
% 4.05/0.99  
% 4.05/0.99  ------ Superposition Options
% 4.05/0.99  
% 4.05/0.99  --superposition_flag                    true
% 4.05/0.99  --sup_passive_queue_type                priority_queues
% 4.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.05/0.99  --demod_completeness_check              fast
% 4.05/0.99  --demod_use_ground                      true
% 4.05/0.99  --sup_to_prop_solver                    passive
% 4.05/0.99  --sup_prop_simpl_new                    true
% 4.05/0.99  --sup_prop_simpl_given                  true
% 4.05/0.99  --sup_fun_splitting                     true
% 4.05/0.99  --sup_smt_interval                      50000
% 4.05/0.99  
% 4.05/0.99  ------ Superposition Simplification Setup
% 4.05/0.99  
% 4.05/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.05/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.05/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.05/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.05/0.99  --sup_immed_triv                        [TrivRules]
% 4.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_immed_bw_main                     []
% 4.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_input_bw                          []
% 4.05/0.99  
% 4.05/0.99  ------ Combination Options
% 4.05/0.99  
% 4.05/0.99  --comb_res_mult                         3
% 4.05/0.99  --comb_sup_mult                         2
% 4.05/0.99  --comb_inst_mult                        10
% 4.05/0.99  
% 4.05/0.99  ------ Debug Options
% 4.05/0.99  
% 4.05/0.99  --dbg_backtrace                         false
% 4.05/0.99  --dbg_dump_prop_clauses                 false
% 4.05/0.99  --dbg_dump_prop_clauses_file            -
% 4.05/0.99  --dbg_out_stat                          false
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  ------ Proving...
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  % SZS status Theorem for theBenchmark.p
% 4.05/0.99  
% 4.05/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.05/0.99  
% 4.05/0.99  fof(f6,axiom,(
% 4.05/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 4.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f18,plain,(
% 4.05/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.05/0.99    inference(ennf_transformation,[],[f6])).
% 4.05/0.99  
% 4.05/0.99  fof(f19,plain,(
% 4.05/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.05/0.99    inference(flattening,[],[f18])).
% 4.05/0.99  
% 4.05/0.99  fof(f53,plain,(
% 4.05/0.99    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f19])).
% 4.05/0.99  
% 4.05/0.99  fof(f1,axiom,(
% 4.05/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f28,plain,(
% 4.05/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.05/0.99    inference(nnf_transformation,[],[f1])).
% 4.05/0.99  
% 4.05/0.99  fof(f29,plain,(
% 4.05/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.05/0.99    inference(flattening,[],[f28])).
% 4.05/0.99  
% 4.05/0.99  fof(f42,plain,(
% 4.05/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.05/0.99    inference(cnf_transformation,[],[f29])).
% 4.05/0.99  
% 4.05/0.99  fof(f74,plain,(
% 4.05/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.05/0.99    inference(equality_resolution,[],[f42])).
% 4.05/0.99  
% 4.05/0.99  fof(f2,axiom,(
% 4.05/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f30,plain,(
% 4.05/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.05/0.99    inference(nnf_transformation,[],[f2])).
% 4.05/0.99  
% 4.05/0.99  fof(f46,plain,(
% 4.05/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f30])).
% 4.05/0.99  
% 4.05/0.99  fof(f11,conjecture,(
% 4.05/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 4.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f12,negated_conjecture,(
% 4.05/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 4.05/0.99    inference(negated_conjecture,[],[f11])).
% 4.05/0.99  
% 4.05/0.99  fof(f26,plain,(
% 4.05/0.99    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 4.05/0.99    inference(ennf_transformation,[],[f12])).
% 4.05/0.99  
% 4.05/0.99  fof(f27,plain,(
% 4.05/0.99    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.05/0.99    inference(flattening,[],[f26])).
% 4.05/0.99  
% 4.05/0.99  fof(f36,plain,(
% 4.05/0.99    ? [X0] : (? [X1] : (? [X2] : ((((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.05/0.99    inference(nnf_transformation,[],[f27])).
% 4.05/0.99  
% 4.05/0.99  fof(f37,plain,(
% 4.05/0.99    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.05/0.99    inference(flattening,[],[f36])).
% 4.05/0.99  
% 4.05/0.99  fof(f40,plain,(
% 4.05/0.99    ( ! [X0,X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK2,X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(sK2,X0) & v1_tsep_1(sK2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2))) )),
% 4.05/0.99    introduced(choice_axiom,[])).
% 4.05/0.99  
% 4.05/0.99  fof(f39,plain,(
% 4.05/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(sK1,X0) | ~v1_tsep_1(sK1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(sK1,X0) & v1_tsep_1(sK1,X0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))) )),
% 4.05/0.99    introduced(choice_axiom,[])).
% 4.05/0.99  
% 4.05/0.99  fof(f38,plain,(
% 4.05/0.99    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_tsep_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_tsep_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 4.05/0.99    introduced(choice_axiom,[])).
% 4.05/0.99  
% 4.05/0.99  fof(f41,plain,(
% 4.05/0.99    (((~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_tsep_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 4.05/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f40,f39,f38])).
% 4.05/0.99  
% 4.05/0.99  fof(f64,plain,(
% 4.05/0.99    l1_pre_topc(sK1)),
% 4.05/0.99    inference(cnf_transformation,[],[f41])).
% 4.05/0.99  
% 4.05/0.99  fof(f4,axiom,(
% 4.05/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f15,plain,(
% 4.05/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.05/0.99    inference(ennf_transformation,[],[f4])).
% 4.05/0.99  
% 4.05/0.99  fof(f48,plain,(
% 4.05/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f15])).
% 4.05/0.99  
% 4.05/0.99  fof(f3,axiom,(
% 4.05/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 4.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f14,plain,(
% 4.05/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 4.05/0.99    inference(ennf_transformation,[],[f3])).
% 4.05/0.99  
% 4.05/0.99  fof(f47,plain,(
% 4.05/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f14])).
% 4.05/0.99  
% 4.05/0.99  fof(f5,axiom,(
% 4.05/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 4.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f16,plain,(
% 4.05/0.99    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.05/0.99    inference(ennf_transformation,[],[f5])).
% 4.05/0.99  
% 4.05/0.99  fof(f17,plain,(
% 4.05/0.99    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.05/0.99    inference(flattening,[],[f16])).
% 4.05/0.99  
% 4.05/0.99  fof(f31,plain,(
% 4.05/0.99    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.05/0.99    inference(nnf_transformation,[],[f17])).
% 4.05/0.99  
% 4.05/0.99  fof(f32,plain,(
% 4.05/0.99    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.05/0.99    inference(flattening,[],[f31])).
% 4.05/0.99  
% 4.05/0.99  fof(f50,plain,(
% 4.05/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f32])).
% 4.05/0.99  
% 4.05/0.99  fof(f66,plain,(
% 4.05/0.99    l1_pre_topc(sK2)),
% 4.05/0.99    inference(cnf_transformation,[],[f41])).
% 4.05/0.99  
% 4.05/0.99  fof(f67,plain,(
% 4.05/0.99    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2),
% 4.05/0.99    inference(cnf_transformation,[],[f41])).
% 4.05/0.99  
% 4.05/0.99  fof(f63,plain,(
% 4.05/0.99    v2_pre_topc(sK1)),
% 4.05/0.99    inference(cnf_transformation,[],[f41])).
% 4.05/0.99  
% 4.05/0.99  fof(f45,plain,(
% 4.05/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.05/0.99    inference(cnf_transformation,[],[f30])).
% 4.05/0.99  
% 4.05/0.99  fof(f52,plain,(
% 4.05/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f32])).
% 4.05/0.99  
% 4.05/0.99  fof(f65,plain,(
% 4.05/0.99    v2_pre_topc(sK2)),
% 4.05/0.99    inference(cnf_transformation,[],[f41])).
% 4.05/0.99  
% 4.05/0.99  fof(f44,plain,(
% 4.05/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f29])).
% 4.05/0.99  
% 4.05/0.99  fof(f9,axiom,(
% 4.05/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 4.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f23,plain,(
% 4.05/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.05/0.99    inference(ennf_transformation,[],[f9])).
% 4.05/0.99  
% 4.05/0.99  fof(f24,plain,(
% 4.05/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.05/0.99    inference(flattening,[],[f23])).
% 4.05/0.99  
% 4.05/0.99  fof(f34,plain,(
% 4.05/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.05/0.99    inference(nnf_transformation,[],[f24])).
% 4.05/0.99  
% 4.05/0.99  fof(f35,plain,(
% 4.05/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.05/0.99    inference(flattening,[],[f34])).
% 4.05/0.99  
% 4.05/0.99  fof(f58,plain,(
% 4.05/0.99    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f35])).
% 4.05/0.99  
% 4.05/0.99  fof(f78,plain,(
% 4.05/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.05/0.99    inference(equality_resolution,[],[f58])).
% 4.05/0.99  
% 4.05/0.99  fof(f10,axiom,(
% 4.05/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f25,plain,(
% 4.05/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.05/0.99    inference(ennf_transformation,[],[f10])).
% 4.05/0.99  
% 4.05/0.99  fof(f60,plain,(
% 4.05/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f25])).
% 4.05/0.99  
% 4.05/0.99  fof(f57,plain,(
% 4.05/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f35])).
% 4.05/0.99  
% 4.05/0.99  fof(f79,plain,(
% 4.05/0.99    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.05/0.99    inference(equality_resolution,[],[f57])).
% 4.05/0.99  
% 4.05/0.99  fof(f70,plain,(
% 4.05/0.99    m1_pre_topc(sK2,sK0) | v1_tsep_1(sK1,sK0)),
% 4.05/0.99    inference(cnf_transformation,[],[f41])).
% 4.05/0.99  
% 4.05/0.99  fof(f62,plain,(
% 4.05/0.99    l1_pre_topc(sK0)),
% 4.05/0.99    inference(cnf_transformation,[],[f41])).
% 4.05/0.99  
% 4.05/0.99  fof(f71,plain,(
% 4.05/0.99    m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 4.05/0.99    inference(cnf_transformation,[],[f41])).
% 4.05/0.99  
% 4.05/0.99  fof(f7,axiom,(
% 4.05/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 4.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f13,plain,(
% 4.05/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 4.05/0.99    inference(pure_predicate_removal,[],[f7])).
% 4.05/0.99  
% 4.05/0.99  fof(f20,plain,(
% 4.05/0.99    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.05/0.99    inference(ennf_transformation,[],[f13])).
% 4.05/0.99  
% 4.05/0.99  fof(f54,plain,(
% 4.05/0.99    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f20])).
% 4.05/0.99  
% 4.05/0.99  fof(f8,axiom,(
% 4.05/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 4.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f21,plain,(
% 4.05/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 4.05/0.99    inference(ennf_transformation,[],[f8])).
% 4.05/0.99  
% 4.05/0.99  fof(f22,plain,(
% 4.05/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.05/0.99    inference(flattening,[],[f21])).
% 4.05/0.99  
% 4.05/0.99  fof(f33,plain,(
% 4.05/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.05/0.99    inference(nnf_transformation,[],[f22])).
% 4.05/0.99  
% 4.05/0.99  fof(f55,plain,(
% 4.05/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f33])).
% 4.05/0.99  
% 4.05/0.99  fof(f76,plain,(
% 4.05/0.99    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 4.05/0.99    inference(equality_resolution,[],[f55])).
% 4.05/0.99  
% 4.05/0.99  fof(f72,plain,(
% 4.05/0.99    ~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)),
% 4.05/0.99    inference(cnf_transformation,[],[f41])).
% 4.05/0.99  
% 4.05/0.99  fof(f68,plain,(
% 4.05/0.99    v1_tsep_1(sK2,sK0) | v1_tsep_1(sK1,sK0)),
% 4.05/0.99    inference(cnf_transformation,[],[f41])).
% 4.05/0.99  
% 4.05/0.99  fof(f61,plain,(
% 4.05/0.99    v2_pre_topc(sK0)),
% 4.05/0.99    inference(cnf_transformation,[],[f41])).
% 4.05/0.99  
% 4.05/0.99  cnf(c_11,plain,
% 4.05/0.99      ( v3_pre_topc(k2_struct_0(X0),X0)
% 4.05/0.99      | ~ v2_pre_topc(X0)
% 4.05/0.99      | ~ l1_pre_topc(X0) ),
% 4.05/0.99      inference(cnf_transformation,[],[f53]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1249,plain,
% 4.05/0.99      ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
% 4.05/0.99      | v2_pre_topc(X0) != iProver_top
% 4.05/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2,plain,
% 4.05/0.99      ( r1_tarski(X0,X0) ),
% 4.05/0.99      inference(cnf_transformation,[],[f74]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1256,plain,
% 4.05/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3,plain,
% 4.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.05/0.99      inference(cnf_transformation,[],[f46]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1255,plain,
% 4.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 4.05/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_27,negated_conjecture,
% 4.05/0.99      ( l1_pre_topc(sK1) ),
% 4.05/0.99      inference(cnf_transformation,[],[f64]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1238,plain,
% 4.05/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_6,plain,
% 4.05/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 4.05/0.99      inference(cnf_transformation,[],[f48]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_5,plain,
% 4.05/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 4.05/0.99      inference(cnf_transformation,[],[f47]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_384,plain,
% 4.05/0.99      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 4.05/0.99      inference(resolution,[status(thm)],[c_6,c_5]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1232,plain,
% 4.05/0.99      ( u1_struct_0(X0) = k2_struct_0(X0)
% 4.05/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1536,plain,
% 4.05/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1238,c_1232]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_9,plain,
% 4.05/0.99      ( ~ v3_pre_topc(X0,X1)
% 4.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 4.05/0.99      | ~ v2_pre_topc(X1)
% 4.05/0.99      | ~ l1_pre_topc(X1) ),
% 4.05/0.99      inference(cnf_transformation,[],[f50]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1251,plain,
% 4.05/0.99      ( v3_pre_topc(X0,X1) != iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
% 4.05/0.99      | v2_pre_topc(X1) != iProver_top
% 4.05/0.99      | l1_pre_topc(X1) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2560,plain,
% 4.05/0.99      ( v3_pre_topc(X0,sK1) != iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.05/0.99      | v2_pre_topc(sK1) != iProver_top
% 4.05/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1536,c_1251]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_25,negated_conjecture,
% 4.05/0.99      ( l1_pre_topc(sK2) ),
% 4.05/0.99      inference(cnf_transformation,[],[f66]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1240,plain,
% 4.05/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1535,plain,
% 4.05/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1240,c_1232]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_24,negated_conjecture,
% 4.05/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
% 4.05/0.99      inference(cnf_transformation,[],[f67]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1713,plain,
% 4.05/0.99      ( g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_1536,c_24]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2566,plain,
% 4.05/0.99      ( v3_pre_topc(X0,sK1) != iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
% 4.05/0.99      | v2_pre_topc(sK1) != iProver_top
% 4.05/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 4.05/0.99      inference(light_normalisation,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_2560,c_1535,c_1536,c_1713]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_28,negated_conjecture,
% 4.05/0.99      ( v2_pre_topc(sK1) ),
% 4.05/0.99      inference(cnf_transformation,[],[f63]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_33,plain,
% 4.05/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_34,plain,
% 4.05/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2872,plain,
% 4.05/0.99      ( v3_pre_topc(X0,sK1) != iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_2566,c_33,c_34]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2878,plain,
% 4.05/0.99      ( v3_pre_topc(X0,sK1) != iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
% 4.05/0.99      | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1255,c_2872]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_4,plain,
% 4.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.05/0.99      inference(cnf_transformation,[],[f45]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1254,plain,
% 4.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.05/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_4862,plain,
% 4.05/0.99      ( v3_pre_topc(X0,sK1) != iProver_top
% 4.05/0.99      | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top
% 4.05/0.99      | r1_tarski(X0,k2_struct_0(sK2)) = iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2878,c_1254]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_6701,plain,
% 4.05/0.99      ( v3_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
% 4.05/0.99      | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) = iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1256,c_4862]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7,plain,
% 4.05/0.99      ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 4.05/0.99      | ~ v2_pre_topc(X1)
% 4.05/0.99      | ~ l1_pre_topc(X1) ),
% 4.05/0.99      inference(cnf_transformation,[],[f52]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1253,plain,
% 4.05/0.99      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
% 4.05/0.99      | v2_pre_topc(X1) != iProver_top
% 4.05/0.99      | l1_pre_topc(X1) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2694,plain,
% 4.05/0.99      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 4.05/0.99      | v2_pre_topc(sK1) != iProver_top
% 4.05/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1536,c_1253]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2699,plain,
% 4.05/0.99      ( v3_pre_topc(X0,sK2) != iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 4.05/0.99      | v2_pre_topc(sK1) != iProver_top
% 4.05/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 4.05/0.99      inference(light_normalisation,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_2694,c_1535,c_1536,c_1713]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2940,plain,
% 4.05/0.99      ( v3_pre_topc(X0,sK2) != iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_2699,c_33,c_34]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2946,plain,
% 4.05/0.99      ( v3_pre_topc(X0,sK2) != iProver_top
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 4.05/0.99      | r1_tarski(X0,k2_struct_0(sK2)) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1255,c_2940]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_4934,plain,
% 4.05/0.99      ( v3_pre_topc(X0,sK2) != iProver_top
% 4.05/0.99      | r1_tarski(X0,k2_struct_0(sK1)) = iProver_top
% 4.05/0.99      | r1_tarski(X0,k2_struct_0(sK2)) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2946,c_1254]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7268,plain,
% 4.05/0.99      ( v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
% 4.05/0.99      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1256,c_4934]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_26,negated_conjecture,
% 4.05/0.99      ( v2_pre_topc(sK2) ),
% 4.05/0.99      inference(cnf_transformation,[],[f65]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_35,plain,
% 4.05/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_36,plain,
% 4.05/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7092,plain,
% 4.05/0.99      ( v3_pre_topc(k2_struct_0(sK2),sK2)
% 4.05/0.99      | ~ v2_pre_topc(sK2)
% 4.05/0.99      | ~ l1_pre_topc(sK2) ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7093,plain,
% 4.05/0.99      ( v3_pre_topc(k2_struct_0(sK2),sK2) = iProver_top
% 4.05/0.99      | v2_pre_topc(sK2) != iProver_top
% 4.05/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_7092]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7275,plain,
% 4.05/0.99      ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_7268,c_35,c_36,c_7093]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_0,plain,
% 4.05/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.05/0.99      inference(cnf_transformation,[],[f44]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1257,plain,
% 4.05/0.99      ( X0 = X1
% 4.05/0.99      | r1_tarski(X0,X1) != iProver_top
% 4.05/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7279,plain,
% 4.05/0.99      ( k2_struct_0(sK1) = k2_struct_0(sK2)
% 4.05/0.99      | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_7275,c_1257]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7350,plain,
% 4.05/0.99      ( k2_struct_0(sK1) = k2_struct_0(sK2)
% 4.05/0.99      | v3_pre_topc(k2_struct_0(sK1),sK1) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_6701,c_7279]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_13273,plain,
% 4.05/0.99      ( k2_struct_0(sK1) = k2_struct_0(sK2)
% 4.05/0.99      | v2_pre_topc(sK1) != iProver_top
% 4.05/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1249,c_7350]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_13352,plain,
% 4.05/0.99      ( k2_struct_0(sK1) = k2_struct_0(sK2) ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_13273,c_33,c_34]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_16,plain,
% 4.05/0.99      ( v1_tsep_1(X0,X1)
% 4.05/0.99      | ~ m1_pre_topc(X0,X1)
% 4.05/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 4.05/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.05/0.99      | ~ v2_pre_topc(X1)
% 4.05/0.99      | ~ l1_pre_topc(X1) ),
% 4.05/0.99      inference(cnf_transformation,[],[f78]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_18,plain,
% 4.05/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.05/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.05/0.99      | ~ l1_pre_topc(X1) ),
% 4.05/0.99      inference(cnf_transformation,[],[f60]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_175,plain,
% 4.05/0.99      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
% 4.05/0.99      | ~ m1_pre_topc(X0,X1)
% 4.05/0.99      | v1_tsep_1(X0,X1)
% 4.05/0.99      | ~ v2_pre_topc(X1)
% 4.05/0.99      | ~ l1_pre_topc(X1) ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_16,c_18]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_176,plain,
% 4.05/0.99      ( v1_tsep_1(X0,X1)
% 4.05/0.99      | ~ m1_pre_topc(X0,X1)
% 4.05/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 4.05/0.99      | ~ v2_pre_topc(X1)
% 4.05/0.99      | ~ l1_pre_topc(X1) ),
% 4.05/0.99      inference(renaming,[status(thm)],[c_175]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1233,plain,
% 4.05/0.99      ( v1_tsep_1(X0,X1) = iProver_top
% 4.05/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 4.05/0.99      | v3_pre_topc(u1_struct_0(X0),X1) != iProver_top
% 4.05/0.99      | v2_pre_topc(X1) != iProver_top
% 4.05/0.99      | l1_pre_topc(X1) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_176]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1847,plain,
% 4.05/0.99      ( v1_tsep_1(sK1,X0) = iProver_top
% 4.05/0.99      | m1_pre_topc(sK1,X0) != iProver_top
% 4.05/0.99      | v3_pre_topc(k2_struct_0(sK1),X0) != iProver_top
% 4.05/0.99      | v2_pre_topc(X0) != iProver_top
% 4.05/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1536,c_1233]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_13397,plain,
% 4.05/0.99      ( v1_tsep_1(sK1,X0) = iProver_top
% 4.05/0.99      | m1_pre_topc(sK1,X0) != iProver_top
% 4.05/0.99      | v3_pre_topc(k2_struct_0(sK2),X0) != iProver_top
% 4.05/0.99      | v2_pre_topc(X0) != iProver_top
% 4.05/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_13352,c_1847]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_13458,plain,
% 4.05/0.99      ( v1_tsep_1(sK1,sK0) = iProver_top
% 4.05/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 4.05/0.99      | v3_pre_topc(k2_struct_0(sK2),sK0) != iProver_top
% 4.05/0.99      | v2_pre_topc(sK0) != iProver_top
% 4.05/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_13397]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_17,plain,
% 4.05/0.99      ( ~ v1_tsep_1(X0,X1)
% 4.05/0.99      | ~ m1_pre_topc(X0,X1)
% 4.05/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 4.05/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.05/0.99      | ~ v2_pre_topc(X1)
% 4.05/0.99      | ~ l1_pre_topc(X1) ),
% 4.05/0.99      inference(cnf_transformation,[],[f79]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_168,plain,
% 4.05/0.99      ( v3_pre_topc(u1_struct_0(X0),X1)
% 4.05/0.99      | ~ m1_pre_topc(X0,X1)
% 4.05/0.99      | ~ v1_tsep_1(X0,X1)
% 4.05/0.99      | ~ v2_pre_topc(X1)
% 4.05/0.99      | ~ l1_pre_topc(X1) ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_17,c_18]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_169,plain,
% 4.05/0.99      ( ~ v1_tsep_1(X0,X1)
% 4.05/0.99      | ~ m1_pre_topc(X0,X1)
% 4.05/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 4.05/0.99      | ~ v2_pre_topc(X1)
% 4.05/0.99      | ~ l1_pre_topc(X1) ),
% 4.05/0.99      inference(renaming,[status(thm)],[c_168]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1234,plain,
% 4.05/0.99      ( v1_tsep_1(X0,X1) != iProver_top
% 4.05/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 4.05/0.99      | v3_pre_topc(u1_struct_0(X0),X1) = iProver_top
% 4.05/0.99      | v2_pre_topc(X1) != iProver_top
% 4.05/0.99      | l1_pre_topc(X1) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_169]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2454,plain,
% 4.05/0.99      ( v1_tsep_1(sK1,X0) != iProver_top
% 4.05/0.99      | m1_pre_topc(sK1,X0) != iProver_top
% 4.05/0.99      | v3_pre_topc(k2_struct_0(sK1),X0) = iProver_top
% 4.05/0.99      | v2_pre_topc(X0) != iProver_top
% 4.05/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1536,c_1234]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_13384,plain,
% 4.05/0.99      ( v1_tsep_1(sK1,X0) != iProver_top
% 4.05/0.99      | m1_pre_topc(sK1,X0) != iProver_top
% 4.05/0.99      | v3_pre_topc(k2_struct_0(sK2),X0) = iProver_top
% 4.05/0.99      | v2_pre_topc(X0) != iProver_top
% 4.05/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_13352,c_2454]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_13451,plain,
% 4.05/0.99      ( v1_tsep_1(sK1,sK0) != iProver_top
% 4.05/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 4.05/0.99      | v3_pre_topc(k2_struct_0(sK2),sK0) = iProver_top
% 4.05/0.99      | v2_pre_topc(sK0) != iProver_top
% 4.05/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_13384]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2456,plain,
% 4.05/0.99      ( v1_tsep_1(sK2,X0) != iProver_top
% 4.05/0.99      | m1_pre_topc(sK2,X0) != iProver_top
% 4.05/0.99      | v3_pre_topc(k2_struct_0(sK2),X0) = iProver_top
% 4.05/0.99      | v2_pre_topc(X0) != iProver_top
% 4.05/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1535,c_1234]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2465,plain,
% 4.05/0.99      ( v1_tsep_1(sK2,sK0) != iProver_top
% 4.05/0.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 4.05/0.99      | v3_pre_topc(k2_struct_0(sK2),sK0) = iProver_top
% 4.05/0.99      | v2_pre_topc(sK0) != iProver_top
% 4.05/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_2456]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_633,plain,
% 4.05/0.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 4.05/0.99      theory(equality) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1886,plain,
% 4.05/0.99      ( ~ l1_pre_topc(X0)
% 4.05/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 4.05/0.99      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != X0 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_633]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2315,plain,
% 4.05/0.99      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 4.05/0.99      | ~ l1_pre_topc(sK2)
% 4.05/0.99      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_1886]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2316,plain,
% 4.05/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
% 4.05/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 4.05/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_2315]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_638,plain,
% 4.05/0.99      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.05/0.99      theory(equality) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1660,plain,
% 4.05/0.99      ( m1_pre_topc(X0,X1)
% 4.05/0.99      | ~ m1_pre_topc(sK2,sK0)
% 4.05/0.99      | X1 != sK0
% 4.05/0.99      | X0 != sK2 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_638]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1923,plain,
% 4.05/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
% 4.05/0.99      | ~ m1_pre_topc(sK2,sK0)
% 4.05/0.99      | X0 != sK0
% 4.05/0.99      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_1660]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1924,plain,
% 4.05/0.99      ( X0 != sK0
% 4.05/0.99      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
% 4.05/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top
% 4.05/0.99      | m1_pre_topc(sK2,sK0) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_1923]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1926,plain,
% 4.05/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
% 4.05/0.99      | sK0 != sK0
% 4.05/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) = iProver_top
% 4.05/0.99      | m1_pre_topc(sK2,sK0) != iProver_top ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_1924]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1849,plain,
% 4.05/0.99      ( v1_tsep_1(sK2,X0) = iProver_top
% 4.05/0.99      | m1_pre_topc(sK2,X0) != iProver_top
% 4.05/0.99      | v3_pre_topc(k2_struct_0(sK2),X0) != iProver_top
% 4.05/0.99      | v2_pre_topc(X0) != iProver_top
% 4.05/0.99      | l1_pre_topc(X0) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1535,c_1233]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1857,plain,
% 4.05/0.99      ( v1_tsep_1(sK2,sK0) = iProver_top
% 4.05/0.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 4.05/0.99      | v3_pre_topc(k2_struct_0(sK2),sK0) != iProver_top
% 4.05/0.99      | v2_pre_topc(sK0) != iProver_top
% 4.05/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_1849]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_21,negated_conjecture,
% 4.05/0.99      ( v1_tsep_1(sK1,sK0) | m1_pre_topc(sK2,sK0) ),
% 4.05/0.99      inference(cnf_transformation,[],[f70]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1243,plain,
% 4.05/0.99      ( v1_tsep_1(sK1,sK0) = iProver_top
% 4.05/0.99      | m1_pre_topc(sK2,sK0) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_29,negated_conjecture,
% 4.05/0.99      ( l1_pre_topc(sK0) ),
% 4.05/0.99      inference(cnf_transformation,[],[f62]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_32,plain,
% 4.05/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_20,negated_conjecture,
% 4.05/0.99      ( m1_pre_topc(sK1,sK0) | m1_pre_topc(sK2,sK0) ),
% 4.05/0.99      inference(cnf_transformation,[],[f71]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_40,plain,
% 4.05/0.99      ( m1_pre_topc(sK1,sK0) = iProver_top
% 4.05/0.99      | m1_pre_topc(sK2,sK0) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_89,plain,
% 4.05/0.99      ( r1_tarski(sK0,sK0) ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_93,plain,
% 4.05/0.99      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_628,plain,( X0 = X0 ),theory(equality) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1384,plain,
% 4.05/0.99      ( sK2 = sK2 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_628]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_629,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1337,plain,
% 4.05/0.99      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_629]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1393,plain,
% 4.05/0.99      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_1337]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1469,plain,
% 4.05/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
% 4.05/0.99      | sK2 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 4.05/0.99      | sK2 != sK2 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_1393]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1307,plain,
% 4.05/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.05/0.99      | m1_pre_topc(sK2,sK0)
% 4.05/0.99      | sK0 != X1
% 4.05/0.99      | sK2 != X0 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_638]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1505,plain,
% 4.05/0.99      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
% 4.05/0.99      | m1_pre_topc(sK2,sK0)
% 4.05/0.99      | sK0 != X0
% 4.05/0.99      | sK2 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_1307]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1506,plain,
% 4.05/0.99      ( sK0 != X0
% 4.05/0.99      | sK2 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 4.05/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 4.05/0.99      | m1_pre_topc(sK2,sK0) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_1505]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1508,plain,
% 4.05/0.99      ( sK0 != sK0
% 4.05/0.99      | sK2 != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 4.05/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) != iProver_top
% 4.05/0.99      | m1_pre_topc(sK2,sK0) = iProver_top ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_1506]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_12,plain,
% 4.05/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.05/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 4.05/0.99      | ~ l1_pre_topc(X1) ),
% 4.05/0.99      inference(cnf_transformation,[],[f54]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1568,plain,
% 4.05/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
% 4.05/0.99      | ~ m1_pre_topc(sK1,sK0)
% 4.05/0.99      | ~ l1_pre_topc(sK0) ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1569,plain,
% 4.05/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) = iProver_top
% 4.05/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 4.05/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_1568]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1675,plain,
% 4.05/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_1243,c_32,c_24,c_40,c_89,c_93,c_1384,c_1469,c_1508,
% 4.05/0.99                 c_1569]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_14,plain,
% 4.05/0.99      ( m1_pre_topc(X0,X1)
% 4.05/0.99      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 4.05/0.99      | ~ v2_pre_topc(X0)
% 4.05/0.99      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 4.05/0.99      | ~ l1_pre_topc(X1)
% 4.05/0.99      | ~ l1_pre_topc(X0)
% 4.05/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 4.05/0.99      inference(cnf_transformation,[],[f76]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1651,plain,
% 4.05/0.99      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
% 4.05/0.99      | m1_pre_topc(sK1,X0)
% 4.05/0.99      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 4.05/0.99      | ~ v2_pre_topc(sK1)
% 4.05/0.99      | ~ l1_pre_topc(X0)
% 4.05/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 4.05/0.99      | ~ l1_pre_topc(sK1) ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1652,plain,
% 4.05/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 4.05/0.99      | m1_pre_topc(sK1,X0) = iProver_top
% 4.05/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 4.05/0.99      | v2_pre_topc(sK1) != iProver_top
% 4.05/0.99      | l1_pre_topc(X0) != iProver_top
% 4.05/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 4.05/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_1651]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1654,plain,
% 4.05/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) != iProver_top
% 4.05/0.99      | m1_pre_topc(sK1,sK0) = iProver_top
% 4.05/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 4.05/0.99      | v2_pre_topc(sK1) != iProver_top
% 4.05/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 4.05/0.99      | l1_pre_topc(sK1) != iProver_top
% 4.05/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_1652]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_637,plain,
% 4.05/0.99      ( ~ v2_pre_topc(X0) | v2_pre_topc(X1) | X1 != X0 ),
% 4.05/0.99      theory(equality) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1415,plain,
% 4.05/0.99      ( ~ v2_pre_topc(X0)
% 4.05/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 4.05/0.99      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X0 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_637]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1574,plain,
% 4.05/0.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 4.05/0.99      | ~ v2_pre_topc(sK2)
% 4.05/0.99      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_1415]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1575,plain,
% 4.05/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
% 4.05/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 4.05/0.99      | v2_pre_topc(sK2) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_1574]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_19,negated_conjecture,
% 4.05/0.99      ( ~ v1_tsep_1(sK1,sK0)
% 4.05/0.99      | ~ v1_tsep_1(sK2,sK0)
% 4.05/0.99      | ~ m1_pre_topc(sK1,sK0)
% 4.05/0.99      | ~ m1_pre_topc(sK2,sK0) ),
% 4.05/0.99      inference(cnf_transformation,[],[f72]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_41,plain,
% 4.05/0.99      ( v1_tsep_1(sK1,sK0) != iProver_top
% 4.05/0.99      | v1_tsep_1(sK2,sK0) != iProver_top
% 4.05/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 4.05/0.99      | m1_pre_topc(sK2,sK0) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_23,negated_conjecture,
% 4.05/0.99      ( v1_tsep_1(sK1,sK0) | v1_tsep_1(sK2,sK0) ),
% 4.05/0.99      inference(cnf_transformation,[],[f68]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_37,plain,
% 4.05/0.99      ( v1_tsep_1(sK1,sK0) = iProver_top
% 4.05/0.99      | v1_tsep_1(sK2,sK0) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_30,negated_conjecture,
% 4.05/0.99      ( v2_pre_topc(sK0) ),
% 4.05/0.99      inference(cnf_transformation,[],[f61]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_31,plain,
% 4.05/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(contradiction,plain,
% 4.05/0.99      ( $false ),
% 4.05/0.99      inference(minisat,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_13458,c_13451,c_2465,c_2316,c_1926,c_1857,c_1675,
% 4.05/0.99                 c_1654,c_1575,c_93,c_89,c_41,c_37,c_24,c_36,c_35,c_34,
% 4.05/0.99                 c_33,c_32,c_31]) ).
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.05/0.99  
% 4.05/0.99  ------                               Statistics
% 4.05/0.99  
% 4.05/0.99  ------ General
% 4.05/0.99  
% 4.05/0.99  abstr_ref_over_cycles:                  0
% 4.05/0.99  abstr_ref_under_cycles:                 0
% 4.05/0.99  gc_basic_clause_elim:                   0
% 4.05/0.99  forced_gc_time:                         0
% 4.05/0.99  parsing_time:                           0.009
% 4.05/0.99  unif_index_cands_time:                  0.
% 4.05/0.99  unif_index_add_time:                    0.
% 4.05/0.99  orderings_time:                         0.
% 4.05/0.99  out_proof_time:                         0.011
% 4.05/0.99  total_time:                             0.464
% 4.05/0.99  num_of_symbols:                         47
% 4.05/0.99  num_of_terms:                           9306
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing
% 4.05/0.99  
% 4.05/0.99  num_of_splits:                          0
% 4.05/0.99  num_of_split_atoms:                     0
% 4.05/0.99  num_of_reused_defs:                     0
% 4.05/0.99  num_eq_ax_congr_red:                    10
% 4.05/0.99  num_of_sem_filtered_clauses:            1
% 4.05/0.99  num_of_subtypes:                        0
% 4.05/0.99  monotx_restored_types:                  0
% 4.05/0.99  sat_num_of_epr_types:                   0
% 4.05/0.99  sat_num_of_non_cyclic_types:            0
% 4.05/0.99  sat_guarded_non_collapsed_types:        0
% 4.05/0.99  num_pure_diseq_elim:                    0
% 4.05/0.99  simp_replaced_by:                       0
% 4.05/0.99  res_preprocessed:                       134
% 4.05/0.99  prep_upred:                             0
% 4.05/0.99  prep_unflattend:                        0
% 4.05/0.99  smt_new_axioms:                         0
% 4.05/0.99  pred_elim_cands:                        7
% 4.05/0.99  pred_elim:                              1
% 4.05/0.99  pred_elim_cl:                           1
% 4.05/0.99  pred_elim_cycles:                       3
% 4.05/0.99  merged_defs:                            8
% 4.05/0.99  merged_defs_ncl:                        0
% 4.05/0.99  bin_hyper_res:                          8
% 4.05/0.99  prep_cycles:                            4
% 4.05/0.99  pred_elim_time:                         0.001
% 4.05/0.99  splitting_time:                         0.
% 4.05/0.99  sem_filter_time:                        0.
% 4.05/0.99  monotx_time:                            0.001
% 4.05/0.99  subtype_inf_time:                       0.
% 4.05/0.99  
% 4.05/0.99  ------ Problem properties
% 4.05/0.99  
% 4.05/0.99  clauses:                                27
% 4.05/0.99  conjectures:                            12
% 4.05/0.99  epr:                                    13
% 4.05/0.99  horn:                                   23
% 4.05/0.99  ground:                                 12
% 4.05/0.99  unary:                                  8
% 4.05/0.99  binary:                                 7
% 4.05/0.99  lits:                                   75
% 4.05/0.99  lits_eq:                                3
% 4.05/0.99  fd_pure:                                0
% 4.05/0.99  fd_pseudo:                              0
% 4.05/0.99  fd_cond:                                0
% 4.05/0.99  fd_pseudo_cond:                         1
% 4.05/0.99  ac_symbols:                             0
% 4.05/0.99  
% 4.05/0.99  ------ Propositional Solver
% 4.05/0.99  
% 4.05/0.99  prop_solver_calls:                      35
% 4.05/0.99  prop_fast_solver_calls:                 1940
% 4.05/0.99  smt_solver_calls:                       0
% 4.05/0.99  smt_fast_solver_calls:                  0
% 4.05/0.99  prop_num_of_clauses:                    5658
% 4.05/0.99  prop_preprocess_simplified:             10903
% 4.05/0.99  prop_fo_subsumed:                       142
% 4.05/0.99  prop_solver_time:                       0.
% 4.05/0.99  smt_solver_time:                        0.
% 4.05/0.99  smt_fast_solver_time:                   0.
% 4.05/0.99  prop_fast_solver_time:                  0.
% 4.05/0.99  prop_unsat_core_time:                   0.
% 4.05/0.99  
% 4.05/0.99  ------ QBF
% 4.05/0.99  
% 4.05/0.99  qbf_q_res:                              0
% 4.05/0.99  qbf_num_tautologies:                    0
% 4.05/0.99  qbf_prep_cycles:                        0
% 4.05/0.99  
% 4.05/0.99  ------ BMC1
% 4.05/0.99  
% 4.05/0.99  bmc1_current_bound:                     -1
% 4.05/0.99  bmc1_last_solved_bound:                 -1
% 4.05/0.99  bmc1_unsat_core_size:                   -1
% 4.05/0.99  bmc1_unsat_core_parents_size:           -1
% 4.05/0.99  bmc1_merge_next_fun:                    0
% 4.05/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.05/0.99  
% 4.05/0.99  ------ Instantiation
% 4.05/0.99  
% 4.05/0.99  inst_num_of_clauses:                    1739
% 4.05/0.99  inst_num_in_passive:                    442
% 4.05/0.99  inst_num_in_active:                     1122
% 4.05/0.99  inst_num_in_unprocessed:                175
% 4.05/0.99  inst_num_of_loops:                      1200
% 4.05/0.99  inst_num_of_learning_restarts:          0
% 4.05/0.99  inst_num_moves_active_passive:          70
% 4.05/0.99  inst_lit_activity:                      0
% 4.05/0.99  inst_lit_activity_moves:                0
% 4.05/0.99  inst_num_tautologies:                   0
% 4.05/0.99  inst_num_prop_implied:                  0
% 4.05/0.99  inst_num_existing_simplified:           0
% 4.05/0.99  inst_num_eq_res_simplified:             0
% 4.05/0.99  inst_num_child_elim:                    0
% 4.05/0.99  inst_num_of_dismatching_blockings:      1599
% 4.05/0.99  inst_num_of_non_proper_insts:           3517
% 4.05/0.99  inst_num_of_duplicates:                 0
% 4.05/0.99  inst_inst_num_from_inst_to_res:         0
% 4.05/0.99  inst_dismatching_checking_time:         0.
% 4.05/0.99  
% 4.05/0.99  ------ Resolution
% 4.05/0.99  
% 4.05/0.99  res_num_of_clauses:                     0
% 4.05/0.99  res_num_in_passive:                     0
% 4.05/0.99  res_num_in_active:                      0
% 4.05/0.99  res_num_of_loops:                       138
% 4.05/0.99  res_forward_subset_subsumed:            445
% 4.05/0.99  res_backward_subset_subsumed:           0
% 4.05/0.99  res_forward_subsumed:                   0
% 4.05/0.99  res_backward_subsumed:                  0
% 4.05/0.99  res_forward_subsumption_resolution:     0
% 4.05/0.99  res_backward_subsumption_resolution:    0
% 4.05/0.99  res_clause_to_clause_subsumption:       1109
% 4.05/0.99  res_orphan_elimination:                 0
% 4.05/0.99  res_tautology_del:                      444
% 4.05/0.99  res_num_eq_res_simplified:              0
% 4.05/0.99  res_num_sel_changes:                    0
% 4.05/0.99  res_moves_from_active_to_pass:          0
% 4.05/0.99  
% 4.05/0.99  ------ Superposition
% 4.05/0.99  
% 4.05/0.99  sup_time_total:                         0.
% 4.05/0.99  sup_time_generating:                    0.
% 4.05/0.99  sup_time_sim_full:                      0.
% 4.05/0.99  sup_time_sim_immed:                     0.
% 4.05/0.99  
% 4.05/0.99  sup_num_of_clauses:                     271
% 4.05/0.99  sup_num_in_active:                      162
% 4.05/0.99  sup_num_in_passive:                     109
% 4.05/0.99  sup_num_of_loops:                       239
% 4.05/0.99  sup_fw_superposition:                   578
% 4.05/0.99  sup_bw_superposition:                   242
% 4.05/0.99  sup_immediate_simplified:               351
% 4.05/0.99  sup_given_eliminated:                   0
% 4.05/0.99  comparisons_done:                       0
% 4.05/0.99  comparisons_avoided:                    0
% 4.05/0.99  
% 4.05/0.99  ------ Simplifications
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  sim_fw_subset_subsumed:                 93
% 4.05/0.99  sim_bw_subset_subsumed:                 36
% 4.05/0.99  sim_fw_subsumed:                        123
% 4.05/0.99  sim_bw_subsumed:                        15
% 4.05/0.99  sim_fw_subsumption_res:                 0
% 4.05/0.99  sim_bw_subsumption_res:                 0
% 4.05/0.99  sim_tautology_del:                      80
% 4.05/0.99  sim_eq_tautology_del:                   10
% 4.05/0.99  sim_eq_res_simp:                        0
% 4.05/0.99  sim_fw_demodulated:                     8
% 4.05/0.99  sim_bw_demodulated:                     59
% 4.05/0.99  sim_light_normalised:                   193
% 4.05/0.99  sim_joinable_taut:                      0
% 4.05/0.99  sim_joinable_simp:                      0
% 4.05/0.99  sim_ac_normalised:                      0
% 4.05/0.99  sim_smt_subsumption:                    0
% 4.05/0.99  
%------------------------------------------------------------------------------
