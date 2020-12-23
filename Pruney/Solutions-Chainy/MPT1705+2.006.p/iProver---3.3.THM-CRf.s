%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:44 EST 2020

% Result     : Theorem 6.95s
% Output     : CNFRefutation 6.95s
% Verified   : 
% Statistics : Number of formulae       :  174 (1241 expanded)
%              Number of clauses        :  102 ( 369 expanded)
%              Number of leaves         :   19 ( 301 expanded)
%              Depth                    :   25
%              Number of atoms          :  735 (10955 expanded)
%              Number of equality atoms :  236 (1339 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f53,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f42,f41,f40])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f75,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f76,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,
    ( v1_tsep_1(sK2,sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_9,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1206,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1211,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1232,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1211,c_3])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1191,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_8,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1207,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1959,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_1207])).

cnf(c_7,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1208,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2321,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1959,c_1208])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1205,plain,
    ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4265,plain,
    ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2321,c_1205])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1193,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1958,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1193,c_1207])).

cnf(c_2320,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_1958,c_1208])).

cnf(c_26,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2599,plain,
    ( g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2321,c_26])).

cnf(c_4295,plain,
    ( v4_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4265,c_2320,c_2321,c_2599])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_35,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_36,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4509,plain,
    ( v4_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4295,c_35,c_36])).

cnf(c_4519,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_4509])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1209,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4826,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4519,c_1209])).

cnf(c_12,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1203,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3198,plain,
    ( v4_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2321,c_1203])).

cnf(c_3239,plain,
    ( v4_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3198,c_2320,c_2321,c_2599])).

cnf(c_3691,plain,
    ( v4_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3239,c_35,c_36])).

cnf(c_3701,plain,
    ( v4_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_3691])).

cnf(c_3891,plain,
    ( v4_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3701,c_1209])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1213,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5070,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK1)
    | v4_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3891,c_1213])).

cnf(c_10454,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK1)
    | v4_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
    | v4_pre_topc(k2_struct_0(sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4826,c_5070])).

cnf(c_13578,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK1)
    | v4_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1206,c_10454])).

cnf(c_14210,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK1)
    | v4_pre_topc(k2_struct_0(sK2),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13578,c_35,c_36])).

cnf(c_14216,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK1)
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1206,c_14210])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_37,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_38,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_14226,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14216,c_37,c_38])).

cnf(c_19,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_303,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_20])).

cnf(c_304,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_303])).

cnf(c_1187,plain,
    ( v1_tsep_1(X0,X1) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_2600,plain,
    ( v1_tsep_1(sK1,X0) != iProver_top
    | v3_pre_topc(k2_struct_0(sK1),X0) = iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2321,c_1187])).

cnf(c_14242,plain,
    ( v1_tsep_1(sK1,X0) != iProver_top
    | v3_pre_topc(k2_struct_0(sK2),X0) = iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14226,c_2600])).

cnf(c_14398,plain,
    ( v1_tsep_1(sK1,sK0) != iProver_top
    | v3_pre_topc(k2_struct_0(sK2),sK0) = iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14242])).

cnf(c_18,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_312,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_20])).

cnf(c_313,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_312])).

cnf(c_1186,plain,
    ( v1_tsep_1(X0,X1) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_2601,plain,
    ( v1_tsep_1(sK1,X0) = iProver_top
    | v3_pre_topc(k2_struct_0(sK1),X0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2321,c_1186])).

cnf(c_14235,plain,
    ( v1_tsep_1(sK1,X0) = iProver_top
    | v3_pre_topc(k2_struct_0(sK2),X0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14226,c_2601])).

cnf(c_14392,plain,
    ( v1_tsep_1(sK1,sK0) = iProver_top
    | v3_pre_topc(k2_struct_0(sK2),sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14235])).

cnf(c_549,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2394,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK2,sK0)
    | X1 != sK0
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_549])).

cnf(c_3863,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
    | ~ m1_pre_topc(sK2,sK0)
    | X0 != sK0
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2 ),
    inference(instantiation,[status(thm)],[c_2394])).

cnf(c_3864,plain,
    ( X0 != sK0
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3863])).

cnf(c_3866,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
    | sK0 != sK0
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3864])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK1,sK0)
    | m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1197,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1201,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2978,plain,
    ( m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2321,c_1201])).

cnf(c_2996,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2978,c_2599])).

cnf(c_3261,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_2996])).

cnf(c_2571,plain,
    ( v1_tsep_1(sK2,X0) = iProver_top
    | v3_pre_topc(k2_struct_0(sK2),X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2320,c_1186])).

cnf(c_2596,plain,
    ( v1_tsep_1(sK2,sK0) = iProver_top
    | v3_pre_topc(k2_struct_0(sK2),sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2571])).

cnf(c_2570,plain,
    ( v1_tsep_1(sK2,X0) != iProver_top
    | v3_pre_topc(k2_struct_0(sK2),X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2320,c_1187])).

cnf(c_2593,plain,
    ( v1_tsep_1(sK2,sK0) != iProver_top
    | v3_pre_topc(k2_struct_0(sK2),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2570])).

cnf(c_546,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2246,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_546,c_26])).

cnf(c_2247,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2246])).

cnf(c_544,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2074,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_544,c_26])).

cnf(c_2075,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2074])).

cnf(c_16,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1613,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1614,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1613])).

cnf(c_99,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_95,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_21,negated_conjecture,
    ( ~ v1_tsep_1(sK1,sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_43,plain,
    ( v1_tsep_1(sK1,sK0) != iProver_top
    | v1_tsep_1(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_25,negated_conjecture,
    ( v1_tsep_1(sK1,sK0)
    | v1_tsep_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_39,plain,
    ( v1_tsep_1(sK1,sK0) = iProver_top
    | v1_tsep_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_34,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14398,c_14392,c_3866,c_3261,c_2596,c_2593,c_2247,c_2075,c_1614,c_99,c_95,c_43,c_39,c_26,c_38,c_37,c_36,c_35,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:03:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 6.95/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.95/1.49  
% 6.95/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.95/1.49  
% 6.95/1.49  ------  iProver source info
% 6.95/1.49  
% 6.95/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.95/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.95/1.49  git: non_committed_changes: false
% 6.95/1.49  git: last_make_outside_of_git: false
% 6.95/1.49  
% 6.95/1.49  ------ 
% 6.95/1.49  ------ Parsing...
% 6.95/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.95/1.49  
% 6.95/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 6.95/1.49  
% 6.95/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.95/1.49  
% 6.95/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.95/1.49  ------ Proving...
% 6.95/1.49  ------ Problem Properties 
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  clauses                                 30
% 6.95/1.49  conjectures                             12
% 6.95/1.49  EPR                                     14
% 6.95/1.49  Horn                                    26
% 6.95/1.49  unary                                   10
% 6.95/1.49  binary                                  8
% 6.95/1.49  lits                                    79
% 6.95/1.49  lits eq                                 4
% 6.95/1.49  fd_pure                                 0
% 6.95/1.49  fd_pseudo                               0
% 6.95/1.49  fd_cond                                 0
% 6.95/1.49  fd_pseudo_cond                          1
% 6.95/1.49  AC symbols                              0
% 6.95/1.49  
% 6.95/1.49  ------ Input Options Time Limit: Unbounded
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  ------ 
% 6.95/1.49  Current options:
% 6.95/1.49  ------ 
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  ------ Proving...
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  % SZS status Theorem for theBenchmark.p
% 6.95/1.49  
% 6.95/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.95/1.49  
% 6.95/1.49  fof(f7,axiom,(
% 6.95/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f18,plain,(
% 6.95/1.49    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 6.95/1.49    inference(ennf_transformation,[],[f7])).
% 6.95/1.49  
% 6.95/1.49  fof(f19,plain,(
% 6.95/1.49    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.95/1.49    inference(flattening,[],[f18])).
% 6.95/1.49  
% 6.95/1.49  fof(f53,plain,(
% 6.95/1.49    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f19])).
% 6.95/1.49  
% 6.95/1.49  fof(f3,axiom,(
% 6.95/1.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f48,plain,(
% 6.95/1.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 6.95/1.49    inference(cnf_transformation,[],[f3])).
% 6.95/1.49  
% 6.95/1.49  fof(f2,axiom,(
% 6.95/1.49    ! [X0] : k2_subset_1(X0) = X0),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f47,plain,(
% 6.95/1.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 6.95/1.49    inference(cnf_transformation,[],[f2])).
% 6.95/1.49  
% 6.95/1.49  fof(f13,conjecture,(
% 6.95/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f14,negated_conjecture,(
% 6.95/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 6.95/1.49    inference(negated_conjecture,[],[f13])).
% 6.95/1.49  
% 6.95/1.49  fof(f28,plain,(
% 6.95/1.49    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 6.95/1.49    inference(ennf_transformation,[],[f14])).
% 6.95/1.49  
% 6.95/1.49  fof(f29,plain,(
% 6.95/1.49    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.95/1.49    inference(flattening,[],[f28])).
% 6.95/1.49  
% 6.95/1.49  fof(f38,plain,(
% 6.95/1.49    ? [X0] : (? [X1] : (? [X2] : ((((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.95/1.49    inference(nnf_transformation,[],[f29])).
% 6.95/1.49  
% 6.95/1.49  fof(f39,plain,(
% 6.95/1.49    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.95/1.49    inference(flattening,[],[f38])).
% 6.95/1.49  
% 6.95/1.49  fof(f42,plain,(
% 6.95/1.49    ( ! [X0,X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK2,X0) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(sK2,X0) & v1_tsep_1(sK2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2))) )),
% 6.95/1.49    introduced(choice_axiom,[])).
% 6.95/1.49  
% 6.95/1.49  fof(f41,plain,(
% 6.95/1.49    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(sK1,X0) | ~v1_tsep_1(sK1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(sK1,X0) & v1_tsep_1(sK1,X0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))) )),
% 6.95/1.49    introduced(choice_axiom,[])).
% 6.95/1.49  
% 6.95/1.49  fof(f40,plain,(
% 6.95/1.49    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_tsep_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_tsep_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 6.95/1.49    introduced(choice_axiom,[])).
% 6.95/1.49  
% 6.95/1.49  fof(f43,plain,(
% 6.95/1.49    (((~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_tsep_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 6.95/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f42,f41,f40])).
% 6.95/1.49  
% 6.95/1.49  fof(f68,plain,(
% 6.95/1.49    l1_pre_topc(sK1)),
% 6.95/1.49    inference(cnf_transformation,[],[f43])).
% 6.95/1.49  
% 6.95/1.49  fof(f6,axiom,(
% 6.95/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f17,plain,(
% 6.95/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 6.95/1.49    inference(ennf_transformation,[],[f6])).
% 6.95/1.49  
% 6.95/1.49  fof(f52,plain,(
% 6.95/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f17])).
% 6.95/1.49  
% 6.95/1.49  fof(f5,axiom,(
% 6.95/1.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f16,plain,(
% 6.95/1.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 6.95/1.49    inference(ennf_transformation,[],[f5])).
% 6.95/1.49  
% 6.95/1.49  fof(f51,plain,(
% 6.95/1.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f16])).
% 6.95/1.49  
% 6.95/1.49  fof(f8,axiom,(
% 6.95/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f20,plain,(
% 6.95/1.49    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 6.95/1.49    inference(ennf_transformation,[],[f8])).
% 6.95/1.49  
% 6.95/1.49  fof(f21,plain,(
% 6.95/1.49    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.95/1.49    inference(flattening,[],[f20])).
% 6.95/1.49  
% 6.95/1.49  fof(f33,plain,(
% 6.95/1.49    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.95/1.49    inference(nnf_transformation,[],[f21])).
% 6.95/1.49  
% 6.95/1.49  fof(f34,plain,(
% 6.95/1.49    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.95/1.49    inference(flattening,[],[f33])).
% 6.95/1.49  
% 6.95/1.49  fof(f57,plain,(
% 6.95/1.49    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f34])).
% 6.95/1.49  
% 6.95/1.49  fof(f70,plain,(
% 6.95/1.49    l1_pre_topc(sK2)),
% 6.95/1.49    inference(cnf_transformation,[],[f43])).
% 6.95/1.49  
% 6.95/1.49  fof(f71,plain,(
% 6.95/1.49    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2),
% 6.95/1.49    inference(cnf_transformation,[],[f43])).
% 6.95/1.49  
% 6.95/1.49  fof(f67,plain,(
% 6.95/1.49    v2_pre_topc(sK1)),
% 6.95/1.49    inference(cnf_transformation,[],[f43])).
% 6.95/1.49  
% 6.95/1.49  fof(f4,axiom,(
% 6.95/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f32,plain,(
% 6.95/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.95/1.49    inference(nnf_transformation,[],[f4])).
% 6.95/1.49  
% 6.95/1.49  fof(f49,plain,(
% 6.95/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.95/1.49    inference(cnf_transformation,[],[f32])).
% 6.95/1.49  
% 6.95/1.49  fof(f55,plain,(
% 6.95/1.49    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f34])).
% 6.95/1.49  
% 6.95/1.49  fof(f1,axiom,(
% 6.95/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f30,plain,(
% 6.95/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.95/1.49    inference(nnf_transformation,[],[f1])).
% 6.95/1.49  
% 6.95/1.49  fof(f31,plain,(
% 6.95/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.95/1.49    inference(flattening,[],[f30])).
% 6.95/1.49  
% 6.95/1.49  fof(f46,plain,(
% 6.95/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f31])).
% 6.95/1.49  
% 6.95/1.49  fof(f69,plain,(
% 6.95/1.49    v2_pre_topc(sK2)),
% 6.95/1.49    inference(cnf_transformation,[],[f43])).
% 6.95/1.49  
% 6.95/1.49  fof(f11,axiom,(
% 6.95/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f25,plain,(
% 6.95/1.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 6.95/1.49    inference(ennf_transformation,[],[f11])).
% 6.95/1.49  
% 6.95/1.49  fof(f26,plain,(
% 6.95/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.95/1.49    inference(flattening,[],[f25])).
% 6.95/1.49  
% 6.95/1.49  fof(f36,plain,(
% 6.95/1.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.95/1.49    inference(nnf_transformation,[],[f26])).
% 6.95/1.49  
% 6.95/1.49  fof(f37,plain,(
% 6.95/1.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.95/1.49    inference(flattening,[],[f36])).
% 6.95/1.49  
% 6.95/1.49  fof(f61,plain,(
% 6.95/1.49    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f37])).
% 6.95/1.49  
% 6.95/1.49  fof(f83,plain,(
% 6.95/1.49    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.95/1.49    inference(equality_resolution,[],[f61])).
% 6.95/1.49  
% 6.95/1.49  fof(f12,axiom,(
% 6.95/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f27,plain,(
% 6.95/1.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 6.95/1.49    inference(ennf_transformation,[],[f12])).
% 6.95/1.49  
% 6.95/1.49  fof(f64,plain,(
% 6.95/1.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f27])).
% 6.95/1.49  
% 6.95/1.49  fof(f62,plain,(
% 6.95/1.49    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f37])).
% 6.95/1.49  
% 6.95/1.49  fof(f82,plain,(
% 6.95/1.49    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.95/1.49    inference(equality_resolution,[],[f62])).
% 6.95/1.49  
% 6.95/1.49  fof(f75,plain,(
% 6.95/1.49    m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 6.95/1.49    inference(cnf_transformation,[],[f43])).
% 6.95/1.49  
% 6.95/1.49  fof(f9,axiom,(
% 6.95/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f15,plain,(
% 6.95/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 6.95/1.49    inference(pure_predicate_removal,[],[f9])).
% 6.95/1.49  
% 6.95/1.49  fof(f22,plain,(
% 6.95/1.49    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 6.95/1.49    inference(ennf_transformation,[],[f15])).
% 6.95/1.49  
% 6.95/1.49  fof(f58,plain,(
% 6.95/1.49    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f22])).
% 6.95/1.49  
% 6.95/1.49  fof(f10,axiom,(
% 6.95/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 6.95/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.95/1.49  
% 6.95/1.49  fof(f23,plain,(
% 6.95/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 6.95/1.49    inference(ennf_transformation,[],[f10])).
% 6.95/1.49  
% 6.95/1.49  fof(f24,plain,(
% 6.95/1.49    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 6.95/1.49    inference(flattening,[],[f23])).
% 6.95/1.49  
% 6.95/1.49  fof(f35,plain,(
% 6.95/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 6.95/1.49    inference(nnf_transformation,[],[f24])).
% 6.95/1.49  
% 6.95/1.49  fof(f59,plain,(
% 6.95/1.49    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 6.95/1.49    inference(cnf_transformation,[],[f35])).
% 6.95/1.49  
% 6.95/1.49  fof(f80,plain,(
% 6.95/1.49    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 6.95/1.49    inference(equality_resolution,[],[f59])).
% 6.95/1.49  
% 6.95/1.49  fof(f44,plain,(
% 6.95/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.95/1.49    inference(cnf_transformation,[],[f31])).
% 6.95/1.49  
% 6.95/1.49  fof(f78,plain,(
% 6.95/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.95/1.49    inference(equality_resolution,[],[f44])).
% 6.95/1.49  
% 6.95/1.49  fof(f76,plain,(
% 6.95/1.49    ~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)),
% 6.95/1.49    inference(cnf_transformation,[],[f43])).
% 6.95/1.49  
% 6.95/1.49  fof(f72,plain,(
% 6.95/1.49    v1_tsep_1(sK2,sK0) | v1_tsep_1(sK1,sK0)),
% 6.95/1.49    inference(cnf_transformation,[],[f43])).
% 6.95/1.49  
% 6.95/1.49  fof(f66,plain,(
% 6.95/1.49    l1_pre_topc(sK0)),
% 6.95/1.49    inference(cnf_transformation,[],[f43])).
% 6.95/1.49  
% 6.95/1.49  fof(f65,plain,(
% 6.95/1.49    v2_pre_topc(sK0)),
% 6.95/1.49    inference(cnf_transformation,[],[f43])).
% 6.95/1.49  
% 6.95/1.49  cnf(c_9,plain,
% 6.95/1.49      ( v4_pre_topc(k2_struct_0(X0),X0)
% 6.95/1.49      | ~ v2_pre_topc(X0)
% 6.95/1.49      | ~ l1_pre_topc(X0) ),
% 6.95/1.49      inference(cnf_transformation,[],[f53]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1206,plain,
% 6.95/1.49      ( v4_pre_topc(k2_struct_0(X0),X0) = iProver_top
% 6.95/1.49      | v2_pre_topc(X0) != iProver_top
% 6.95/1.49      | l1_pre_topc(X0) != iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_4,plain,
% 6.95/1.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 6.95/1.49      inference(cnf_transformation,[],[f48]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1211,plain,
% 6.95/1.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3,plain,
% 6.95/1.49      ( k2_subset_1(X0) = X0 ),
% 6.95/1.49      inference(cnf_transformation,[],[f47]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1232,plain,
% 6.95/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 6.95/1.49      inference(light_normalisation,[status(thm)],[c_1211,c_3]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_29,negated_conjecture,
% 6.95/1.49      ( l1_pre_topc(sK1) ),
% 6.95/1.49      inference(cnf_transformation,[],[f68]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1191,plain,
% 6.95/1.49      ( l1_pre_topc(sK1) = iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_8,plain,
% 6.95/1.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 6.95/1.49      inference(cnf_transformation,[],[f52]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1207,plain,
% 6.95/1.49      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1959,plain,
% 6.95/1.49      ( l1_struct_0(sK1) = iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_1191,c_1207]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_7,plain,
% 6.95/1.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 6.95/1.49      inference(cnf_transformation,[],[f51]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1208,plain,
% 6.95/1.49      ( u1_struct_0(X0) = k2_struct_0(X0)
% 6.95/1.49      | l1_struct_0(X0) != iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2321,plain,
% 6.95/1.49      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_1959,c_1208]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_10,plain,
% 6.95/1.49      ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.95/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 6.95/1.49      | ~ v2_pre_topc(X1)
% 6.95/1.49      | ~ l1_pre_topc(X1) ),
% 6.95/1.49      inference(cnf_transformation,[],[f57]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1205,plain,
% 6.95/1.49      ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
% 6.95/1.49      | v2_pre_topc(X1) != iProver_top
% 6.95/1.49      | l1_pre_topc(X1) != iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_4265,plain,
% 6.95/1.49      ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 6.95/1.49      | v2_pre_topc(sK1) != iProver_top
% 6.95/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_2321,c_1205]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_27,negated_conjecture,
% 6.95/1.49      ( l1_pre_topc(sK2) ),
% 6.95/1.49      inference(cnf_transformation,[],[f70]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1193,plain,
% 6.95/1.49      ( l1_pre_topc(sK2) = iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1958,plain,
% 6.95/1.49      ( l1_struct_0(sK2) = iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_1193,c_1207]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2320,plain,
% 6.95/1.49      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_1958,c_1208]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_26,negated_conjecture,
% 6.95/1.49      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
% 6.95/1.49      inference(cnf_transformation,[],[f71]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2599,plain,
% 6.95/1.49      ( g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
% 6.95/1.49      inference(demodulation,[status(thm)],[c_2321,c_26]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_4295,plain,
% 6.95/1.49      ( v4_pre_topc(X0,sK2) != iProver_top
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 6.95/1.49      | v2_pre_topc(sK1) != iProver_top
% 6.95/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 6.95/1.49      inference(light_normalisation,
% 6.95/1.49                [status(thm)],
% 6.95/1.49                [c_4265,c_2320,c_2321,c_2599]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_30,negated_conjecture,
% 6.95/1.49      ( v2_pre_topc(sK1) ),
% 6.95/1.49      inference(cnf_transformation,[],[f67]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_35,plain,
% 6.95/1.49      ( v2_pre_topc(sK1) = iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_36,plain,
% 6.95/1.49      ( l1_pre_topc(sK1) = iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_4509,plain,
% 6.95/1.49      ( v4_pre_topc(X0,sK2) != iProver_top
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 6.95/1.49      inference(global_propositional_subsumption,
% 6.95/1.49                [status(thm)],
% 6.95/1.49                [c_4295,c_35,c_36]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_4519,plain,
% 6.95/1.49      ( v4_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
% 6.95/1.49      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_1232,c_4509]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_6,plain,
% 6.95/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 6.95/1.49      inference(cnf_transformation,[],[f49]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1209,plain,
% 6.95/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.95/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_4826,plain,
% 6.95/1.49      ( v4_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
% 6.95/1.49      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_4519,c_1209]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_12,plain,
% 6.95/1.49      ( ~ v4_pre_topc(X0,X1)
% 6.95/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 6.95/1.49      | ~ v2_pre_topc(X1)
% 6.95/1.49      | ~ l1_pre_topc(X1) ),
% 6.95/1.49      inference(cnf_transformation,[],[f55]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1203,plain,
% 6.95/1.49      ( v4_pre_topc(X0,X1) != iProver_top
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
% 6.95/1.49      | v2_pre_topc(X1) != iProver_top
% 6.95/1.49      | l1_pre_topc(X1) != iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3198,plain,
% 6.95/1.49      ( v4_pre_topc(X0,sK1) != iProver_top
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 6.95/1.49      | v2_pre_topc(sK1) != iProver_top
% 6.95/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_2321,c_1203]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3239,plain,
% 6.95/1.49      ( v4_pre_topc(X0,sK1) != iProver_top
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
% 6.95/1.49      | v2_pre_topc(sK1) != iProver_top
% 6.95/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 6.95/1.49      inference(light_normalisation,
% 6.95/1.49                [status(thm)],
% 6.95/1.49                [c_3198,c_2320,c_2321,c_2599]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3691,plain,
% 6.95/1.49      ( v4_pre_topc(X0,sK1) != iProver_top
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 6.95/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 6.95/1.49      inference(global_propositional_subsumption,
% 6.95/1.49                [status(thm)],
% 6.95/1.49                [c_3239,c_35,c_36]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3701,plain,
% 6.95/1.49      ( v4_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
% 6.95/1.49      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_1232,c_3691]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3891,plain,
% 6.95/1.49      ( v4_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
% 6.95/1.49      | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) = iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_3701,c_1209]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_0,plain,
% 6.95/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 6.95/1.49      inference(cnf_transformation,[],[f46]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1213,plain,
% 6.95/1.49      ( X0 = X1
% 6.95/1.49      | r1_tarski(X0,X1) != iProver_top
% 6.95/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_5070,plain,
% 6.95/1.49      ( k2_struct_0(sK2) = k2_struct_0(sK1)
% 6.95/1.49      | v4_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
% 6.95/1.49      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) != iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_3891,c_1213]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_10454,plain,
% 6.95/1.49      ( k2_struct_0(sK2) = k2_struct_0(sK1)
% 6.95/1.49      | v4_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
% 6.95/1.49      | v4_pre_topc(k2_struct_0(sK2),sK2) != iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_4826,c_5070]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_13578,plain,
% 6.95/1.49      ( k2_struct_0(sK2) = k2_struct_0(sK1)
% 6.95/1.49      | v4_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
% 6.95/1.49      | v2_pre_topc(sK1) != iProver_top
% 6.95/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_1206,c_10454]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_14210,plain,
% 6.95/1.49      ( k2_struct_0(sK2) = k2_struct_0(sK1)
% 6.95/1.49      | v4_pre_topc(k2_struct_0(sK2),sK2) != iProver_top ),
% 6.95/1.49      inference(global_propositional_subsumption,
% 6.95/1.49                [status(thm)],
% 6.95/1.49                [c_13578,c_35,c_36]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_14216,plain,
% 6.95/1.49      ( k2_struct_0(sK2) = k2_struct_0(sK1)
% 6.95/1.49      | v2_pre_topc(sK2) != iProver_top
% 6.95/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_1206,c_14210]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_28,negated_conjecture,
% 6.95/1.49      ( v2_pre_topc(sK2) ),
% 6.95/1.49      inference(cnf_transformation,[],[f69]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_37,plain,
% 6.95/1.49      ( v2_pre_topc(sK2) = iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_38,plain,
% 6.95/1.49      ( l1_pre_topc(sK2) = iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_14226,plain,
% 6.95/1.49      ( k2_struct_0(sK2) = k2_struct_0(sK1) ),
% 6.95/1.49      inference(global_propositional_subsumption,
% 6.95/1.49                [status(thm)],
% 6.95/1.49                [c_14216,c_37,c_38]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_19,plain,
% 6.95/1.49      ( ~ v1_tsep_1(X0,X1)
% 6.95/1.49      | v3_pre_topc(u1_struct_0(X0),X1)
% 6.95/1.49      | ~ m1_pre_topc(X0,X1)
% 6.95/1.49      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 6.95/1.49      | ~ v2_pre_topc(X1)
% 6.95/1.49      | ~ l1_pre_topc(X1) ),
% 6.95/1.49      inference(cnf_transformation,[],[f83]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_20,plain,
% 6.95/1.49      ( ~ m1_pre_topc(X0,X1)
% 6.95/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 6.95/1.49      | ~ l1_pre_topc(X1) ),
% 6.95/1.49      inference(cnf_transformation,[],[f64]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_303,plain,
% 6.95/1.49      ( ~ m1_pre_topc(X0,X1)
% 6.95/1.49      | v3_pre_topc(u1_struct_0(X0),X1)
% 6.95/1.49      | ~ v1_tsep_1(X0,X1)
% 6.95/1.49      | ~ v2_pre_topc(X1)
% 6.95/1.49      | ~ l1_pre_topc(X1) ),
% 6.95/1.49      inference(global_propositional_subsumption,
% 6.95/1.49                [status(thm)],
% 6.95/1.49                [c_19,c_20]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_304,plain,
% 6.95/1.49      ( ~ v1_tsep_1(X0,X1)
% 6.95/1.49      | v3_pre_topc(u1_struct_0(X0),X1)
% 6.95/1.49      | ~ m1_pre_topc(X0,X1)
% 6.95/1.49      | ~ v2_pre_topc(X1)
% 6.95/1.49      | ~ l1_pre_topc(X1) ),
% 6.95/1.49      inference(renaming,[status(thm)],[c_303]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1187,plain,
% 6.95/1.49      ( v1_tsep_1(X0,X1) != iProver_top
% 6.95/1.49      | v3_pre_topc(u1_struct_0(X0),X1) = iProver_top
% 6.95/1.49      | m1_pre_topc(X0,X1) != iProver_top
% 6.95/1.49      | v2_pre_topc(X1) != iProver_top
% 6.95/1.49      | l1_pre_topc(X1) != iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2600,plain,
% 6.95/1.49      ( v1_tsep_1(sK1,X0) != iProver_top
% 6.95/1.49      | v3_pre_topc(k2_struct_0(sK1),X0) = iProver_top
% 6.95/1.49      | m1_pre_topc(sK1,X0) != iProver_top
% 6.95/1.49      | v2_pre_topc(X0) != iProver_top
% 6.95/1.49      | l1_pre_topc(X0) != iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_2321,c_1187]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_14242,plain,
% 6.95/1.49      ( v1_tsep_1(sK1,X0) != iProver_top
% 6.95/1.49      | v3_pre_topc(k2_struct_0(sK2),X0) = iProver_top
% 6.95/1.49      | m1_pre_topc(sK1,X0) != iProver_top
% 6.95/1.49      | v2_pre_topc(X0) != iProver_top
% 6.95/1.49      | l1_pre_topc(X0) != iProver_top ),
% 6.95/1.49      inference(demodulation,[status(thm)],[c_14226,c_2600]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_14398,plain,
% 6.95/1.49      ( v1_tsep_1(sK1,sK0) != iProver_top
% 6.95/1.49      | v3_pre_topc(k2_struct_0(sK2),sK0) = iProver_top
% 6.95/1.49      | m1_pre_topc(sK1,sK0) != iProver_top
% 6.95/1.49      | v2_pre_topc(sK0) != iProver_top
% 6.95/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 6.95/1.49      inference(instantiation,[status(thm)],[c_14242]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_18,plain,
% 6.95/1.49      ( v1_tsep_1(X0,X1)
% 6.95/1.49      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 6.95/1.49      | ~ m1_pre_topc(X0,X1)
% 6.95/1.49      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 6.95/1.49      | ~ v2_pre_topc(X1)
% 6.95/1.49      | ~ l1_pre_topc(X1) ),
% 6.95/1.49      inference(cnf_transformation,[],[f82]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_312,plain,
% 6.95/1.49      ( ~ m1_pre_topc(X0,X1)
% 6.95/1.49      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 6.95/1.49      | v1_tsep_1(X0,X1)
% 6.95/1.49      | ~ v2_pre_topc(X1)
% 6.95/1.49      | ~ l1_pre_topc(X1) ),
% 6.95/1.49      inference(global_propositional_subsumption,
% 6.95/1.49                [status(thm)],
% 6.95/1.49                [c_18,c_20]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_313,plain,
% 6.95/1.49      ( v1_tsep_1(X0,X1)
% 6.95/1.49      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 6.95/1.49      | ~ m1_pre_topc(X0,X1)
% 6.95/1.49      | ~ v2_pre_topc(X1)
% 6.95/1.49      | ~ l1_pre_topc(X1) ),
% 6.95/1.49      inference(renaming,[status(thm)],[c_312]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1186,plain,
% 6.95/1.49      ( v1_tsep_1(X0,X1) = iProver_top
% 6.95/1.49      | v3_pre_topc(u1_struct_0(X0),X1) != iProver_top
% 6.95/1.49      | m1_pre_topc(X0,X1) != iProver_top
% 6.95/1.49      | v2_pre_topc(X1) != iProver_top
% 6.95/1.49      | l1_pre_topc(X1) != iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2601,plain,
% 6.95/1.49      ( v1_tsep_1(sK1,X0) = iProver_top
% 6.95/1.49      | v3_pre_topc(k2_struct_0(sK1),X0) != iProver_top
% 6.95/1.49      | m1_pre_topc(sK1,X0) != iProver_top
% 6.95/1.49      | v2_pre_topc(X0) != iProver_top
% 6.95/1.49      | l1_pre_topc(X0) != iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_2321,c_1186]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_14235,plain,
% 6.95/1.49      ( v1_tsep_1(sK1,X0) = iProver_top
% 6.95/1.49      | v3_pre_topc(k2_struct_0(sK2),X0) != iProver_top
% 6.95/1.49      | m1_pre_topc(sK1,X0) != iProver_top
% 6.95/1.49      | v2_pre_topc(X0) != iProver_top
% 6.95/1.49      | l1_pre_topc(X0) != iProver_top ),
% 6.95/1.49      inference(demodulation,[status(thm)],[c_14226,c_2601]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_14392,plain,
% 6.95/1.49      ( v1_tsep_1(sK1,sK0) = iProver_top
% 6.95/1.49      | v3_pre_topc(k2_struct_0(sK2),sK0) != iProver_top
% 6.95/1.49      | m1_pre_topc(sK1,sK0) != iProver_top
% 6.95/1.49      | v2_pre_topc(sK0) != iProver_top
% 6.95/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 6.95/1.49      inference(instantiation,[status(thm)],[c_14235]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_549,plain,
% 6.95/1.49      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.95/1.49      theory(equality) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2394,plain,
% 6.95/1.49      ( m1_pre_topc(X0,X1)
% 6.95/1.49      | ~ m1_pre_topc(sK2,sK0)
% 6.95/1.49      | X1 != sK0
% 6.95/1.49      | X0 != sK2 ),
% 6.95/1.49      inference(instantiation,[status(thm)],[c_549]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3863,plain,
% 6.95/1.49      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
% 6.95/1.49      | ~ m1_pre_topc(sK2,sK0)
% 6.95/1.49      | X0 != sK0
% 6.95/1.49      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2 ),
% 6.95/1.49      inference(instantiation,[status(thm)],[c_2394]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3864,plain,
% 6.95/1.49      ( X0 != sK0
% 6.95/1.49      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
% 6.95/1.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top
% 6.95/1.49      | m1_pre_topc(sK2,sK0) != iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_3863]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3866,plain,
% 6.95/1.49      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK2
% 6.95/1.49      | sK0 != sK0
% 6.95/1.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) = iProver_top
% 6.95/1.49      | m1_pre_topc(sK2,sK0) != iProver_top ),
% 6.95/1.49      inference(instantiation,[status(thm)],[c_3864]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_22,negated_conjecture,
% 6.95/1.49      ( m1_pre_topc(sK1,sK0) | m1_pre_topc(sK2,sK0) ),
% 6.95/1.49      inference(cnf_transformation,[],[f75]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1197,plain,
% 6.95/1.49      ( m1_pre_topc(sK1,sK0) = iProver_top
% 6.95/1.49      | m1_pre_topc(sK2,sK0) = iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_14,plain,
% 6.95/1.49      ( ~ m1_pre_topc(X0,X1)
% 6.95/1.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 6.95/1.49      | ~ l1_pre_topc(X1) ),
% 6.95/1.49      inference(cnf_transformation,[],[f58]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1201,plain,
% 6.95/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 6.95/1.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 6.95/1.49      | l1_pre_topc(X1) != iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2978,plain,
% 6.95/1.49      ( m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top
% 6.95/1.49      | m1_pre_topc(sK1,X0) != iProver_top
% 6.95/1.49      | l1_pre_topc(X0) != iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_2321,c_1201]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2996,plain,
% 6.95/1.49      ( m1_pre_topc(sK1,X0) != iProver_top
% 6.95/1.49      | m1_pre_topc(sK2,X0) = iProver_top
% 6.95/1.49      | l1_pre_topc(X0) != iProver_top ),
% 6.95/1.49      inference(light_normalisation,[status(thm)],[c_2978,c_2599]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_3261,plain,
% 6.95/1.49      ( m1_pre_topc(sK2,sK0) = iProver_top
% 6.95/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_1197,c_2996]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2571,plain,
% 6.95/1.49      ( v1_tsep_1(sK2,X0) = iProver_top
% 6.95/1.49      | v3_pre_topc(k2_struct_0(sK2),X0) != iProver_top
% 6.95/1.49      | m1_pre_topc(sK2,X0) != iProver_top
% 6.95/1.49      | v2_pre_topc(X0) != iProver_top
% 6.95/1.49      | l1_pre_topc(X0) != iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_2320,c_1186]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2596,plain,
% 6.95/1.49      ( v1_tsep_1(sK2,sK0) = iProver_top
% 6.95/1.49      | v3_pre_topc(k2_struct_0(sK2),sK0) != iProver_top
% 6.95/1.49      | m1_pre_topc(sK2,sK0) != iProver_top
% 6.95/1.49      | v2_pre_topc(sK0) != iProver_top
% 6.95/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 6.95/1.49      inference(instantiation,[status(thm)],[c_2571]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2570,plain,
% 6.95/1.49      ( v1_tsep_1(sK2,X0) != iProver_top
% 6.95/1.49      | v3_pre_topc(k2_struct_0(sK2),X0) = iProver_top
% 6.95/1.49      | m1_pre_topc(sK2,X0) != iProver_top
% 6.95/1.49      | v2_pre_topc(X0) != iProver_top
% 6.95/1.49      | l1_pre_topc(X0) != iProver_top ),
% 6.95/1.49      inference(superposition,[status(thm)],[c_2320,c_1187]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2593,plain,
% 6.95/1.49      ( v1_tsep_1(sK2,sK0) != iProver_top
% 6.95/1.49      | v3_pre_topc(k2_struct_0(sK2),sK0) = iProver_top
% 6.95/1.49      | m1_pre_topc(sK2,sK0) != iProver_top
% 6.95/1.49      | v2_pre_topc(sK0) != iProver_top
% 6.95/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 6.95/1.49      inference(instantiation,[status(thm)],[c_2570]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_546,plain,
% 6.95/1.49      ( ~ v2_pre_topc(X0) | v2_pre_topc(X1) | X1 != X0 ),
% 6.95/1.49      theory(equality) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2246,plain,
% 6.95/1.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 6.95/1.49      | ~ v2_pre_topc(sK2) ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_546,c_26]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2247,plain,
% 6.95/1.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 6.95/1.49      | v2_pre_topc(sK2) != iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_2246]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_544,plain,
% 6.95/1.49      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 6.95/1.49      theory(equality) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2074,plain,
% 6.95/1.49      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 6.95/1.49      | ~ l1_pre_topc(sK2) ),
% 6.95/1.49      inference(resolution,[status(thm)],[c_544,c_26]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2075,plain,
% 6.95/1.49      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 6.95/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_2074]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_16,plain,
% 6.95/1.49      ( m1_pre_topc(X0,X1)
% 6.95/1.49      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 6.95/1.49      | ~ v2_pre_topc(X0)
% 6.95/1.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 6.95/1.49      | ~ l1_pre_topc(X1)
% 6.95/1.49      | ~ l1_pre_topc(X0)
% 6.95/1.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 6.95/1.49      inference(cnf_transformation,[],[f80]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1613,plain,
% 6.95/1.49      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
% 6.95/1.49      | m1_pre_topc(sK1,sK0)
% 6.95/1.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 6.95/1.49      | ~ v2_pre_topc(sK1)
% 6.95/1.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 6.95/1.49      | ~ l1_pre_topc(sK1)
% 6.95/1.49      | ~ l1_pre_topc(sK0) ),
% 6.95/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_1614,plain,
% 6.95/1.49      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) != iProver_top
% 6.95/1.49      | m1_pre_topc(sK1,sK0) = iProver_top
% 6.95/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 6.95/1.49      | v2_pre_topc(sK1) != iProver_top
% 6.95/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 6.95/1.49      | l1_pre_topc(sK1) != iProver_top
% 6.95/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_1613]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_99,plain,
% 6.95/1.49      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 6.95/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_2,plain,
% 6.95/1.49      ( r1_tarski(X0,X0) ),
% 6.95/1.49      inference(cnf_transformation,[],[f78]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_95,plain,
% 6.95/1.49      ( r1_tarski(sK0,sK0) ),
% 6.95/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_21,negated_conjecture,
% 6.95/1.49      ( ~ v1_tsep_1(sK1,sK0)
% 6.95/1.49      | ~ v1_tsep_1(sK2,sK0)
% 6.95/1.49      | ~ m1_pre_topc(sK1,sK0)
% 6.95/1.49      | ~ m1_pre_topc(sK2,sK0) ),
% 6.95/1.49      inference(cnf_transformation,[],[f76]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_43,plain,
% 6.95/1.49      ( v1_tsep_1(sK1,sK0) != iProver_top
% 6.95/1.49      | v1_tsep_1(sK2,sK0) != iProver_top
% 6.95/1.49      | m1_pre_topc(sK1,sK0) != iProver_top
% 6.95/1.49      | m1_pre_topc(sK2,sK0) != iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_25,negated_conjecture,
% 6.95/1.49      ( v1_tsep_1(sK1,sK0) | v1_tsep_1(sK2,sK0) ),
% 6.95/1.49      inference(cnf_transformation,[],[f72]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_39,plain,
% 6.95/1.49      ( v1_tsep_1(sK1,sK0) = iProver_top
% 6.95/1.49      | v1_tsep_1(sK2,sK0) = iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_31,negated_conjecture,
% 6.95/1.49      ( l1_pre_topc(sK0) ),
% 6.95/1.49      inference(cnf_transformation,[],[f66]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_34,plain,
% 6.95/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_32,negated_conjecture,
% 6.95/1.49      ( v2_pre_topc(sK0) ),
% 6.95/1.49      inference(cnf_transformation,[],[f65]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(c_33,plain,
% 6.95/1.49      ( v2_pre_topc(sK0) = iProver_top ),
% 6.95/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 6.95/1.49  
% 6.95/1.49  cnf(contradiction,plain,
% 6.95/1.49      ( $false ),
% 6.95/1.49      inference(minisat,
% 6.95/1.49                [status(thm)],
% 6.95/1.49                [c_14398,c_14392,c_3866,c_3261,c_2596,c_2593,c_2247,
% 6.95/1.49                 c_2075,c_1614,c_99,c_95,c_43,c_39,c_26,c_38,c_37,c_36,
% 6.95/1.49                 c_35,c_34,c_33]) ).
% 6.95/1.49  
% 6.95/1.49  
% 6.95/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 6.95/1.49  
% 6.95/1.49  ------                               Statistics
% 6.95/1.49  
% 6.95/1.49  ------ Selected
% 6.95/1.49  
% 6.95/1.49  total_time:                             0.589
% 6.95/1.49  
%------------------------------------------------------------------------------
