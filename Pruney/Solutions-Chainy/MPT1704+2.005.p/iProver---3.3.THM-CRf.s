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
% DateTime   : Thu Dec  3 12:21:43 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :  169 (2530 expanded)
%              Number of clauses        :  101 ( 773 expanded)
%              Number of leaves         :   15 ( 608 expanded)
%              Depth                    :   24
%              Number of atoms          :  751 (21569 expanded)
%              Number of equality atoms :  270 (2696 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f12,conjecture,(
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
                    & v1_borsuk_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
                      & v1_borsuk_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,X0)
            | ~ v1_borsuk_1(X2,X0)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_borsuk_1(X1,X0) )
          & ( ( m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0) )
            | ( m1_pre_topc(X1,X0)
              & v1_borsuk_1(X1,X0) ) )
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
     => ( ( ~ m1_pre_topc(sK2,X0)
          | ~ v1_borsuk_1(sK2,X0)
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
        & ( ( m1_pre_topc(sK2,X0)
            & v1_borsuk_1(sK2,X0) )
          | ( m1_pre_topc(X1,X0)
            & v1_borsuk_1(X1,X0) ) )
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = sK2
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | ~ m1_pre_topc(sK1,X0)
              | ~ v1_borsuk_1(sK1,X0) )
            & ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0) )
              | ( m1_pre_topc(sK1,X0)
                & v1_borsuk_1(sK1,X0) ) )
            & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ v1_borsuk_1(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) )
                  | ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) ) )
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
                | ~ v1_borsuk_1(X2,sK0)
                | ~ m1_pre_topc(X1,sK0)
                | ~ v1_borsuk_1(X1,sK0) )
              & ( ( m1_pre_topc(X2,sK0)
                  & v1_borsuk_1(X2,sK0) )
                | ( m1_pre_topc(X1,sK0)
                  & v1_borsuk_1(X1,sK0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ m1_pre_topc(sK2,sK0)
      | ~ v1_borsuk_1(sK2,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_borsuk_1(sK1,sK0) )
    & ( ( m1_pre_topc(sK2,sK0)
        & v1_borsuk_1(sK2,sK0) )
      | ( m1_pre_topc(sK1,sK0)
        & v1_borsuk_1(sK1,sK0) ) )
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).

fof(f64,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

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

fof(f30,plain,(
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
    inference(flattening,[],[f30])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f54,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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
                    & v1_borsuk_1(X1,X0) )
                <=> v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f71,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f22])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f78,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f72,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_borsuk_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,
    ( v1_borsuk_1(sK2,sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1199,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1220,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1199,c_3])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1179,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1195,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1911,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_1195])).

cnf(c_7,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1196,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2331,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1911,c_1196])).

cnf(c_9,plain,
    ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1194,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4538,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2331,c_1194])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1181,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1910,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1181,c_1195])).

cnf(c_2330,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_1910,c_1196])).

cnf(c_25,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2621,plain,
    ( g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2331,c_25])).

cnf(c_4568,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4538,c_2330,c_2331,c_2621])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_34,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_35,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4837,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4568,c_34,c_35])).

cnf(c_4847,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_4837])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1197,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5125,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4847,c_1197])).

cnf(c_11,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1192,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3324,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2331,c_1192])).

cnf(c_3365,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3324,c_2330,c_2331,c_2621])).

cnf(c_3992,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3365,c_34,c_35])).

cnf(c_4002,plain,
    ( v3_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_3992])).

cnf(c_4249,plain,
    ( v3_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4002,c_1197])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1201,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5352,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK1)
    | v3_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4249,c_1201])).

cnf(c_10834,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK1)
    | v3_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
    | v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5125,c_5352])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_36,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_37,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_13,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1190,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1187,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3062,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1187,c_1197])).

cnf(c_6907,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2330,c_3062])).

cnf(c_7319,plain,
    ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6907,c_37])).

cnf(c_7320,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7319])).

cnf(c_7327,plain,
    ( m1_pre_topc(sK1,sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2331,c_7320])).

cnf(c_7365,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK1)
    | m1_pre_topc(sK1,sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7327,c_1201])).

cnf(c_9587,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK1)
    | m1_pre_topc(sK1,sK2) != iProver_top
    | v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5125,c_7365])).

cnf(c_14248,plain,
    ( v3_pre_topc(k2_struct_0(sK1),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_14253,plain,
    ( v3_pre_topc(k2_struct_0(sK1),sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14248])).

cnf(c_15170,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK1)
    | v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9587,c_34,c_35,c_10834,c_14253])).

cnf(c_15176,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK1)
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1190,c_15170])).

cnf(c_15186,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10834,c_36,c_37,c_15176])).

cnf(c_16,plain,
    ( ~ v1_borsuk_1(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_294,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_borsuk_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_19])).

cnf(c_295,plain,
    ( ~ v1_borsuk_1(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_294])).

cnf(c_1175,plain,
    ( v1_borsuk_1(X0,X1) != iProver_top
    | v4_pre_topc(u1_struct_0(X0),X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_295])).

cnf(c_2622,plain,
    ( v1_borsuk_1(sK1,X0) != iProver_top
    | v4_pre_topc(k2_struct_0(sK1),X0) = iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2331,c_1175])).

cnf(c_15202,plain,
    ( v1_borsuk_1(sK1,X0) != iProver_top
    | v4_pre_topc(k2_struct_0(sK2),X0) = iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15186,c_2622])).

cnf(c_15358,plain,
    ( v1_borsuk_1(sK1,sK0) != iProver_top
    | v4_pre_topc(k2_struct_0(sK2),sK0) = iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_15202])).

cnf(c_15,plain,
    ( v1_borsuk_1(X0,X1)
    | ~ v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_303,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v4_pre_topc(u1_struct_0(X0),X1)
    | v1_borsuk_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_19])).

cnf(c_304,plain,
    ( v1_borsuk_1(X0,X1)
    | ~ v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_303])).

cnf(c_1174,plain,
    ( v1_borsuk_1(X0,X1) = iProver_top
    | v4_pre_topc(u1_struct_0(X0),X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_2623,plain,
    ( v1_borsuk_1(sK1,X0) = iProver_top
    | v4_pre_topc(k2_struct_0(sK1),X0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2331,c_1174])).

cnf(c_15195,plain,
    ( v1_borsuk_1(sK1,X0) = iProver_top
    | v4_pre_topc(k2_struct_0(sK2),X0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15186,c_2623])).

cnf(c_15352,plain,
    ( v1_borsuk_1(sK1,sK0) = iProver_top
    | v4_pre_topc(k2_struct_0(sK2),sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_15195])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK1,sK0)
    | m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1185,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1189,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4630,plain,
    ( m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2331,c_1189])).

cnf(c_4671,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4630,c_2331,c_2621])).

cnf(c_4964,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4671,c_34,c_35,c_36,c_37])).

cnf(c_4973,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1185,c_4964])).

cnf(c_18,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1188,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4327,plain,
    ( m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(sK1,X0) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2331,c_1188])).

cnf(c_4367,plain,
    ( m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4327,c_2331,c_2621])).

cnf(c_4867,plain,
    ( m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4367,c_34,c_35,c_36,c_37])).

cnf(c_4870,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4867])).

cnf(c_2593,plain,
    ( v1_borsuk_1(sK2,X0) = iProver_top
    | v4_pre_topc(k2_struct_0(sK2),X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2330,c_1174])).

cnf(c_2618,plain,
    ( v1_borsuk_1(sK2,sK0) = iProver_top
    | v4_pre_topc(k2_struct_0(sK2),sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2593])).

cnf(c_2592,plain,
    ( v1_borsuk_1(sK2,X0) != iProver_top
    | v4_pre_topc(k2_struct_0(sK2),X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2330,c_1175])).

cnf(c_2615,plain,
    ( v1_borsuk_1(sK2,sK0) != iProver_top
    | v4_pre_topc(k2_struct_0(sK2),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2592])).

cnf(c_20,negated_conjecture,
    ( ~ v1_borsuk_1(sK1,sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_42,plain,
    ( v1_borsuk_1(sK1,sK0) != iProver_top
    | v1_borsuk_1(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_24,negated_conjecture,
    ( v1_borsuk_1(sK1,sK0)
    | v1_borsuk_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_38,plain,
    ( v1_borsuk_1(sK1,sK0) = iProver_top
    | v1_borsuk_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_33,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_32,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15358,c_15352,c_4973,c_4870,c_2618,c_2615,c_42,c_38,c_33,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:59:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.04/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/0.98  
% 4.04/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.04/0.98  
% 4.04/0.98  ------  iProver source info
% 4.04/0.98  
% 4.04/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.04/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.04/0.98  git: non_committed_changes: false
% 4.04/0.98  git: last_make_outside_of_git: false
% 4.04/0.98  
% 4.04/0.98  ------ 
% 4.04/0.98  ------ Parsing...
% 4.04/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.04/0.98  
% 4.04/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.04/0.98  
% 4.04/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.04/0.98  
% 4.04/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.04/0.98  ------ Proving...
% 4.04/0.98  ------ Problem Properties 
% 4.04/0.98  
% 4.04/0.98  
% 4.04/0.98  clauses                                 30
% 4.04/0.98  conjectures                             12
% 4.04/0.98  EPR                                     14
% 4.04/0.98  Horn                                    26
% 4.04/0.98  unary                                   10
% 4.04/0.98  binary                                  8
% 4.04/0.98  lits                                    83
% 4.04/0.98  lits eq                                 4
% 4.04/0.98  fd_pure                                 0
% 4.04/0.98  fd_pseudo                               0
% 4.04/0.98  fd_cond                                 0
% 4.04/0.98  fd_pseudo_cond                          1
% 4.04/0.98  AC symbols                              0
% 4.04/0.98  
% 4.04/0.98  ------ Input Options Time Limit: Unbounded
% 4.04/0.98  
% 4.04/0.98  
% 4.04/0.98  ------ 
% 4.04/0.98  Current options:
% 4.04/0.98  ------ 
% 4.04/0.98  
% 4.04/0.98  
% 4.04/0.98  
% 4.04/0.98  
% 4.04/0.98  ------ Proving...
% 4.04/0.98  
% 4.04/0.98  
% 4.04/0.98  % SZS status Theorem for theBenchmark.p
% 4.04/0.98  
% 4.04/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.04/0.98  
% 4.04/0.98  fof(f3,axiom,(
% 4.04/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 4.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.98  
% 4.04/0.98  fof(f45,plain,(
% 4.04/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 4.04/0.98    inference(cnf_transformation,[],[f3])).
% 4.04/0.98  
% 4.04/0.98  fof(f2,axiom,(
% 4.04/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 4.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.98  
% 4.04/0.98  fof(f44,plain,(
% 4.04/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 4.04/0.98    inference(cnf_transformation,[],[f2])).
% 4.04/0.98  
% 4.04/0.98  fof(f12,conjecture,(
% 4.04/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 4.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.98  
% 4.04/0.98  fof(f13,negated_conjecture,(
% 4.04/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 4.04/0.98    inference(negated_conjecture,[],[f12])).
% 4.04/0.98  
% 4.04/0.98  fof(f25,plain,(
% 4.04/0.98    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 4.04/0.98    inference(ennf_transformation,[],[f13])).
% 4.04/0.98  
% 4.04/0.98  fof(f26,plain,(
% 4.04/0.98    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.04/0.98    inference(flattening,[],[f25])).
% 4.04/0.98  
% 4.04/0.98  fof(f35,plain,(
% 4.04/0.98    ? [X0] : (? [X1] : (? [X2] : ((((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.04/0.98    inference(nnf_transformation,[],[f26])).
% 4.04/0.98  
% 4.04/0.98  fof(f36,plain,(
% 4.04/0.98    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.04/0.98    inference(flattening,[],[f35])).
% 4.04/0.98  
% 4.04/0.98  fof(f39,plain,(
% 4.04/0.98    ( ! [X0,X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK2,X0) | ~v1_borsuk_1(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(sK2,X0) & v1_borsuk_1(sK2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2))) )),
% 4.04/0.98    introduced(choice_axiom,[])).
% 4.04/0.98  
% 4.04/0.98  fof(f38,plain,(
% 4.04/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(sK1,X0) | ~v1_borsuk_1(sK1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(sK1,X0) & v1_borsuk_1(sK1,X0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))) )),
% 4.04/0.98    introduced(choice_axiom,[])).
% 4.04/0.98  
% 4.04/0.98  fof(f37,plain,(
% 4.04/0.98    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_borsuk_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_borsuk_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 4.04/0.98    introduced(choice_axiom,[])).
% 4.04/0.98  
% 4.04/0.98  fof(f40,plain,(
% 4.04/0.98    (((~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_borsuk_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 4.04/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).
% 4.04/0.98  
% 4.04/0.98  fof(f64,plain,(
% 4.04/0.98    l1_pre_topc(sK1)),
% 4.04/0.98    inference(cnf_transformation,[],[f40])).
% 4.04/0.98  
% 4.04/0.98  fof(f6,axiom,(
% 4.04/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.98  
% 4.04/0.98  fof(f15,plain,(
% 4.04/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.04/0.98    inference(ennf_transformation,[],[f6])).
% 4.04/0.98  
% 4.04/0.98  fof(f49,plain,(
% 4.04/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 4.04/0.98    inference(cnf_transformation,[],[f15])).
% 4.04/0.98  
% 4.04/0.98  fof(f5,axiom,(
% 4.04/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 4.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.98  
% 4.04/0.98  fof(f14,plain,(
% 4.04/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 4.04/0.98    inference(ennf_transformation,[],[f5])).
% 4.04/0.98  
% 4.04/0.98  fof(f48,plain,(
% 4.04/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 4.04/0.98    inference(cnf_transformation,[],[f14])).
% 4.04/0.98  
% 4.04/0.98  fof(f7,axiom,(
% 4.04/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 4.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.98  
% 4.04/0.98  fof(f16,plain,(
% 4.04/0.98    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.04/0.98    inference(ennf_transformation,[],[f7])).
% 4.04/0.98  
% 4.04/0.98  fof(f17,plain,(
% 4.04/0.98    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.04/0.98    inference(flattening,[],[f16])).
% 4.04/0.98  
% 4.04/0.98  fof(f30,plain,(
% 4.04/0.98    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.04/0.98    inference(nnf_transformation,[],[f17])).
% 4.04/0.98  
% 4.04/0.98  fof(f31,plain,(
% 4.04/0.98    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.04/0.98    inference(flattening,[],[f30])).
% 4.04/0.98  
% 4.04/0.98  fof(f53,plain,(
% 4.04/0.98    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.04/0.98    inference(cnf_transformation,[],[f31])).
% 4.04/0.98  
% 4.04/0.98  fof(f66,plain,(
% 4.04/0.98    l1_pre_topc(sK2)),
% 4.04/0.98    inference(cnf_transformation,[],[f40])).
% 4.04/0.98  
% 4.04/0.98  fof(f67,plain,(
% 4.04/0.98    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2),
% 4.04/0.98    inference(cnf_transformation,[],[f40])).
% 4.04/0.98  
% 4.04/0.98  fof(f63,plain,(
% 4.04/0.98    v2_pre_topc(sK1)),
% 4.04/0.98    inference(cnf_transformation,[],[f40])).
% 4.04/0.98  
% 4.04/0.98  fof(f4,axiom,(
% 4.04/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.98  
% 4.04/0.98  fof(f29,plain,(
% 4.04/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.04/0.98    inference(nnf_transformation,[],[f4])).
% 4.04/0.98  
% 4.04/0.98  fof(f46,plain,(
% 4.04/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.04/0.98    inference(cnf_transformation,[],[f29])).
% 4.04/0.98  
% 4.04/0.98  fof(f51,plain,(
% 4.04/0.98    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.04/0.98    inference(cnf_transformation,[],[f31])).
% 4.04/0.98  
% 4.04/0.98  fof(f1,axiom,(
% 4.04/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.98  
% 4.04/0.98  fof(f27,plain,(
% 4.04/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.04/0.98    inference(nnf_transformation,[],[f1])).
% 4.04/0.98  
% 4.04/0.98  fof(f28,plain,(
% 4.04/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.04/0.98    inference(flattening,[],[f27])).
% 4.04/0.98  
% 4.04/0.98  fof(f43,plain,(
% 4.04/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.04/0.98    inference(cnf_transformation,[],[f28])).
% 4.04/0.98  
% 4.04/0.98  fof(f65,plain,(
% 4.04/0.98    v2_pre_topc(sK2)),
% 4.04/0.98    inference(cnf_transformation,[],[f40])).
% 4.04/0.98  
% 4.04/0.98  fof(f8,axiom,(
% 4.04/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 4.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.98  
% 4.04/0.98  fof(f18,plain,(
% 4.04/0.98    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.04/0.98    inference(ennf_transformation,[],[f8])).
% 4.04/0.98  
% 4.04/0.98  fof(f19,plain,(
% 4.04/0.98    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.04/0.98    inference(flattening,[],[f18])).
% 4.04/0.98  
% 4.04/0.98  fof(f54,plain,(
% 4.04/0.98    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.04/0.98    inference(cnf_transformation,[],[f19])).
% 4.04/0.98  
% 4.04/0.98  fof(f11,axiom,(
% 4.04/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.98  
% 4.04/0.98  fof(f24,plain,(
% 4.04/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.04/0.98    inference(ennf_transformation,[],[f11])).
% 4.04/0.98  
% 4.04/0.98  fof(f60,plain,(
% 4.04/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.04/0.98    inference(cnf_transformation,[],[f24])).
% 4.04/0.98  
% 4.04/0.98  fof(f9,axiom,(
% 4.04/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0))))))),
% 4.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.98  
% 4.04/0.98  fof(f20,plain,(
% 4.04/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.04/0.98    inference(ennf_transformation,[],[f9])).
% 4.04/0.98  
% 4.04/0.98  fof(f21,plain,(
% 4.04/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.04/0.98    inference(flattening,[],[f20])).
% 4.04/0.98  
% 4.04/0.98  fof(f32,plain,(
% 4.04/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.04/0.98    inference(nnf_transformation,[],[f21])).
% 4.04/0.98  
% 4.04/0.98  fof(f33,plain,(
% 4.04/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.04/0.98    inference(flattening,[],[f32])).
% 4.04/0.98  
% 4.04/0.98  fof(f55,plain,(
% 4.04/0.98    ( ! [X2,X0,X1] : (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.04/0.98    inference(cnf_transformation,[],[f33])).
% 4.04/0.98  
% 4.04/0.98  fof(f77,plain,(
% 4.04/0.98    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.04/0.98    inference(equality_resolution,[],[f55])).
% 4.04/0.98  
% 4.04/0.98  fof(f56,plain,(
% 4.04/0.98    ( ! [X2,X0,X1] : (v1_borsuk_1(X1,X0) | ~v4_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.04/0.98    inference(cnf_transformation,[],[f33])).
% 4.04/0.98  
% 4.04/0.98  fof(f76,plain,(
% 4.04/0.98    ( ! [X0,X1] : (v1_borsuk_1(X1,X0) | ~v4_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.04/0.98    inference(equality_resolution,[],[f56])).
% 4.04/0.98  
% 4.04/0.98  fof(f71,plain,(
% 4.04/0.98    m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 4.04/0.98    inference(cnf_transformation,[],[f40])).
% 4.04/0.98  
% 4.04/0.98  fof(f10,axiom,(
% 4.04/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 4.04/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.98  
% 4.04/0.98  fof(f22,plain,(
% 4.04/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 4.04/0.98    inference(ennf_transformation,[],[f10])).
% 4.04/0.98  
% 4.04/0.98  fof(f23,plain,(
% 4.04/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.04/0.98    inference(flattening,[],[f22])).
% 4.04/0.98  
% 4.04/0.98  fof(f34,plain,(
% 4.04/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.04/0.98    inference(nnf_transformation,[],[f23])).
% 4.04/0.98  
% 4.04/0.98  fof(f59,plain,(
% 4.04/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 4.04/0.98    inference(cnf_transformation,[],[f34])).
% 4.04/0.98  
% 4.04/0.98  fof(f78,plain,(
% 4.04/0.98    ( ! [X2,X0] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 4.04/0.98    inference(equality_resolution,[],[f59])).
% 4.04/0.98  
% 4.04/0.98  fof(f58,plain,(
% 4.04/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 4.04/0.98    inference(cnf_transformation,[],[f34])).
% 4.04/0.98  
% 4.04/0.98  fof(f79,plain,(
% 4.04/0.98    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 4.04/0.98    inference(equality_resolution,[],[f58])).
% 4.04/0.98  
% 4.04/0.98  fof(f72,plain,(
% 4.04/0.98    ~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)),
% 4.04/0.98    inference(cnf_transformation,[],[f40])).
% 4.04/0.98  
% 4.04/0.98  fof(f68,plain,(
% 4.04/0.98    v1_borsuk_1(sK2,sK0) | v1_borsuk_1(sK1,sK0)),
% 4.04/0.98    inference(cnf_transformation,[],[f40])).
% 4.04/0.98  
% 4.04/0.98  fof(f62,plain,(
% 4.04/0.98    l1_pre_topc(sK0)),
% 4.04/0.98    inference(cnf_transformation,[],[f40])).
% 4.04/0.98  
% 4.04/0.98  fof(f61,plain,(
% 4.04/0.98    v2_pre_topc(sK0)),
% 4.04/0.98    inference(cnf_transformation,[],[f40])).
% 4.04/0.98  
% 4.04/0.98  cnf(c_4,plain,
% 4.04/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 4.04/0.98      inference(cnf_transformation,[],[f45]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1199,plain,
% 4.04/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_3,plain,
% 4.04/0.98      ( k2_subset_1(X0) = X0 ),
% 4.04/0.98      inference(cnf_transformation,[],[f44]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1220,plain,
% 4.04/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.04/0.98      inference(light_normalisation,[status(thm)],[c_1199,c_3]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_28,negated_conjecture,
% 4.04/0.98      ( l1_pre_topc(sK1) ),
% 4.04/0.98      inference(cnf_transformation,[],[f64]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1179,plain,
% 4.04/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_8,plain,
% 4.04/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 4.04/0.98      inference(cnf_transformation,[],[f49]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1195,plain,
% 4.04/0.98      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1911,plain,
% 4.04/0.98      ( l1_struct_0(sK1) = iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_1179,c_1195]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_7,plain,
% 4.04/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 4.04/0.98      inference(cnf_transformation,[],[f48]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1196,plain,
% 4.04/0.98      ( u1_struct_0(X0) = k2_struct_0(X0)
% 4.04/0.98      | l1_struct_0(X0) != iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_2331,plain,
% 4.04/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_1911,c_1196]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_9,plain,
% 4.04/0.98      ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.04/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 4.04/0.98      | ~ v2_pre_topc(X1)
% 4.04/0.98      | ~ l1_pre_topc(X1) ),
% 4.04/0.98      inference(cnf_transformation,[],[f53]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1194,plain,
% 4.04/0.98      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
% 4.04/0.98      | v2_pre_topc(X1) != iProver_top
% 4.04/0.98      | l1_pre_topc(X1) != iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_4538,plain,
% 4.04/0.98      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 4.04/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.04/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_2331,c_1194]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_26,negated_conjecture,
% 4.04/0.98      ( l1_pre_topc(sK2) ),
% 4.04/0.98      inference(cnf_transformation,[],[f66]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1181,plain,
% 4.04/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1910,plain,
% 4.04/0.98      ( l1_struct_0(sK2) = iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_1181,c_1195]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_2330,plain,
% 4.04/0.98      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_1910,c_1196]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_25,negated_conjecture,
% 4.04/0.98      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
% 4.04/0.98      inference(cnf_transformation,[],[f67]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_2621,plain,
% 4.04/0.98      ( g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
% 4.04/0.98      inference(demodulation,[status(thm)],[c_2331,c_25]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_4568,plain,
% 4.04/0.98      ( v3_pre_topc(X0,sK2) != iProver_top
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 4.04/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.04/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 4.04/0.98      inference(light_normalisation,
% 4.04/0.98                [status(thm)],
% 4.04/0.98                [c_4538,c_2330,c_2331,c_2621]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_29,negated_conjecture,
% 4.04/0.98      ( v2_pre_topc(sK1) ),
% 4.04/0.98      inference(cnf_transformation,[],[f63]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_34,plain,
% 4.04/0.98      ( v2_pre_topc(sK1) = iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_35,plain,
% 4.04/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_4837,plain,
% 4.04/0.98      ( v3_pre_topc(X0,sK2) != iProver_top
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 4.04/0.98      inference(global_propositional_subsumption,
% 4.04/0.98                [status(thm)],
% 4.04/0.98                [c_4568,c_34,c_35]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_4847,plain,
% 4.04/0.98      ( v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
% 4.04/0.98      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_1220,c_4837]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_6,plain,
% 4.04/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.04/0.98      inference(cnf_transformation,[],[f46]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1197,plain,
% 4.04/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.04/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_5125,plain,
% 4.04/0.98      ( v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
% 4.04/0.98      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_4847,c_1197]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_11,plain,
% 4.04/0.98      ( ~ v3_pre_topc(X0,X1)
% 4.04/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 4.04/0.98      | ~ v2_pre_topc(X1)
% 4.04/0.98      | ~ l1_pre_topc(X1) ),
% 4.04/0.98      inference(cnf_transformation,[],[f51]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1192,plain,
% 4.04/0.98      ( v3_pre_topc(X0,X1) != iProver_top
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
% 4.04/0.98      | v2_pre_topc(X1) != iProver_top
% 4.04/0.98      | l1_pre_topc(X1) != iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_3324,plain,
% 4.04/0.98      ( v3_pre_topc(X0,sK1) != iProver_top
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.04/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.04/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_2331,c_1192]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_3365,plain,
% 4.04/0.98      ( v3_pre_topc(X0,sK1) != iProver_top
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
% 4.04/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.04/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 4.04/0.98      inference(light_normalisation,
% 4.04/0.98                [status(thm)],
% 4.04/0.98                [c_3324,c_2330,c_2331,c_2621]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_3992,plain,
% 4.04/0.98      ( v3_pre_topc(X0,sK1) != iProver_top
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 4.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 4.04/0.98      inference(global_propositional_subsumption,
% 4.04/0.98                [status(thm)],
% 4.04/0.98                [c_3365,c_34,c_35]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_4002,plain,
% 4.04/0.98      ( v3_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
% 4.04/0.98      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_1220,c_3992]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_4249,plain,
% 4.04/0.98      ( v3_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
% 4.04/0.98      | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) = iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_4002,c_1197]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_0,plain,
% 4.04/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.04/0.98      inference(cnf_transformation,[],[f43]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1201,plain,
% 4.04/0.98      ( X0 = X1
% 4.04/0.98      | r1_tarski(X0,X1) != iProver_top
% 4.04/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_5352,plain,
% 4.04/0.98      ( k2_struct_0(sK2) = k2_struct_0(sK1)
% 4.04/0.98      | v3_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
% 4.04/0.98      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) != iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_4249,c_1201]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_10834,plain,
% 4.04/0.98      ( k2_struct_0(sK2) = k2_struct_0(sK1)
% 4.04/0.98      | v3_pre_topc(k2_struct_0(sK1),sK1) != iProver_top
% 4.04/0.98      | v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_5125,c_5352]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_27,negated_conjecture,
% 4.04/0.98      ( v2_pre_topc(sK2) ),
% 4.04/0.98      inference(cnf_transformation,[],[f65]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_36,plain,
% 4.04/0.98      ( v2_pre_topc(sK2) = iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_37,plain,
% 4.04/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_13,plain,
% 4.04/0.98      ( v3_pre_topc(k2_struct_0(X0),X0)
% 4.04/0.98      | ~ v2_pre_topc(X0)
% 4.04/0.98      | ~ l1_pre_topc(X0) ),
% 4.04/0.98      inference(cnf_transformation,[],[f54]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1190,plain,
% 4.04/0.98      ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
% 4.04/0.98      | v2_pre_topc(X0) != iProver_top
% 4.04/0.98      | l1_pre_topc(X0) != iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_19,plain,
% 4.04/0.98      ( ~ m1_pre_topc(X0,X1)
% 4.04/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.04/0.98      | ~ l1_pre_topc(X1) ),
% 4.04/0.98      inference(cnf_transformation,[],[f60]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1187,plain,
% 4.04/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 4.04/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 4.04/0.98      | l1_pre_topc(X1) != iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_3062,plain,
% 4.04/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 4.04/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 4.04/0.98      | l1_pre_topc(X1) != iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_1187,c_1197]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_6907,plain,
% 4.04/0.98      ( m1_pre_topc(X0,sK2) != iProver_top
% 4.04/0.98      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
% 4.04/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_2330,c_3062]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_7319,plain,
% 4.04/0.98      ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
% 4.04/0.98      | m1_pre_topc(X0,sK2) != iProver_top ),
% 4.04/0.98      inference(global_propositional_subsumption,
% 4.04/0.98                [status(thm)],
% 4.04/0.98                [c_6907,c_37]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_7320,plain,
% 4.04/0.98      ( m1_pre_topc(X0,sK2) != iProver_top
% 4.04/0.98      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
% 4.04/0.98      inference(renaming,[status(thm)],[c_7319]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_7327,plain,
% 4.04/0.98      ( m1_pre_topc(sK1,sK2) != iProver_top
% 4.04/0.98      | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) = iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_2331,c_7320]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_7365,plain,
% 4.04/0.98      ( k2_struct_0(sK2) = k2_struct_0(sK1)
% 4.04/0.98      | m1_pre_topc(sK1,sK2) != iProver_top
% 4.04/0.98      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) != iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_7327,c_1201]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_9587,plain,
% 4.04/0.98      ( k2_struct_0(sK2) = k2_struct_0(sK1)
% 4.04/0.98      | m1_pre_topc(sK1,sK2) != iProver_top
% 4.04/0.98      | v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_5125,c_7365]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_14248,plain,
% 4.04/0.98      ( v3_pre_topc(k2_struct_0(sK1),sK1)
% 4.04/0.98      | ~ v2_pre_topc(sK1)
% 4.04/0.98      | ~ l1_pre_topc(sK1) ),
% 4.04/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_14253,plain,
% 4.04/0.98      ( v3_pre_topc(k2_struct_0(sK1),sK1) = iProver_top
% 4.04/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.04/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_14248]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_15170,plain,
% 4.04/0.98      ( k2_struct_0(sK2) = k2_struct_0(sK1)
% 4.04/0.98      | v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top ),
% 4.04/0.98      inference(global_propositional_subsumption,
% 4.04/0.98                [status(thm)],
% 4.04/0.98                [c_9587,c_34,c_35,c_10834,c_14253]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_15176,plain,
% 4.04/0.98      ( k2_struct_0(sK2) = k2_struct_0(sK1)
% 4.04/0.98      | v2_pre_topc(sK2) != iProver_top
% 4.04/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_1190,c_15170]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_15186,plain,
% 4.04/0.98      ( k2_struct_0(sK2) = k2_struct_0(sK1) ),
% 4.04/0.98      inference(global_propositional_subsumption,
% 4.04/0.98                [status(thm)],
% 4.04/0.98                [c_10834,c_36,c_37,c_15176]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_16,plain,
% 4.04/0.98      ( ~ v1_borsuk_1(X0,X1)
% 4.04/0.98      | v4_pre_topc(u1_struct_0(X0),X1)
% 4.04/0.98      | ~ m1_pre_topc(X0,X1)
% 4.04/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.04/0.98      | ~ v2_pre_topc(X1)
% 4.04/0.98      | ~ l1_pre_topc(X1) ),
% 4.04/0.98      inference(cnf_transformation,[],[f77]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_294,plain,
% 4.04/0.98      ( ~ m1_pre_topc(X0,X1)
% 4.04/0.98      | v4_pre_topc(u1_struct_0(X0),X1)
% 4.04/0.98      | ~ v1_borsuk_1(X0,X1)
% 4.04/0.98      | ~ v2_pre_topc(X1)
% 4.04/0.98      | ~ l1_pre_topc(X1) ),
% 4.04/0.98      inference(global_propositional_subsumption,
% 4.04/0.98                [status(thm)],
% 4.04/0.98                [c_16,c_19]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_295,plain,
% 4.04/0.98      ( ~ v1_borsuk_1(X0,X1)
% 4.04/0.98      | v4_pre_topc(u1_struct_0(X0),X1)
% 4.04/0.98      | ~ m1_pre_topc(X0,X1)
% 4.04/0.98      | ~ v2_pre_topc(X1)
% 4.04/0.98      | ~ l1_pre_topc(X1) ),
% 4.04/0.98      inference(renaming,[status(thm)],[c_294]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1175,plain,
% 4.04/0.98      ( v1_borsuk_1(X0,X1) != iProver_top
% 4.04/0.98      | v4_pre_topc(u1_struct_0(X0),X1) = iProver_top
% 4.04/0.98      | m1_pre_topc(X0,X1) != iProver_top
% 4.04/0.98      | v2_pre_topc(X1) != iProver_top
% 4.04/0.98      | l1_pre_topc(X1) != iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_295]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_2622,plain,
% 4.04/0.98      ( v1_borsuk_1(sK1,X0) != iProver_top
% 4.04/0.98      | v4_pre_topc(k2_struct_0(sK1),X0) = iProver_top
% 4.04/0.98      | m1_pre_topc(sK1,X0) != iProver_top
% 4.04/0.98      | v2_pre_topc(X0) != iProver_top
% 4.04/0.98      | l1_pre_topc(X0) != iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_2331,c_1175]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_15202,plain,
% 4.04/0.98      ( v1_borsuk_1(sK1,X0) != iProver_top
% 4.04/0.98      | v4_pre_topc(k2_struct_0(sK2),X0) = iProver_top
% 4.04/0.98      | m1_pre_topc(sK1,X0) != iProver_top
% 4.04/0.98      | v2_pre_topc(X0) != iProver_top
% 4.04/0.98      | l1_pre_topc(X0) != iProver_top ),
% 4.04/0.98      inference(demodulation,[status(thm)],[c_15186,c_2622]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_15358,plain,
% 4.04/0.98      ( v1_borsuk_1(sK1,sK0) != iProver_top
% 4.04/0.98      | v4_pre_topc(k2_struct_0(sK2),sK0) = iProver_top
% 4.04/0.98      | m1_pre_topc(sK1,sK0) != iProver_top
% 4.04/0.98      | v2_pre_topc(sK0) != iProver_top
% 4.04/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 4.04/0.98      inference(instantiation,[status(thm)],[c_15202]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_15,plain,
% 4.04/0.98      ( v1_borsuk_1(X0,X1)
% 4.04/0.98      | ~ v4_pre_topc(u1_struct_0(X0),X1)
% 4.04/0.98      | ~ m1_pre_topc(X0,X1)
% 4.04/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.04/0.98      | ~ v2_pre_topc(X1)
% 4.04/0.98      | ~ l1_pre_topc(X1) ),
% 4.04/0.98      inference(cnf_transformation,[],[f76]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_303,plain,
% 4.04/0.98      ( ~ m1_pre_topc(X0,X1)
% 4.04/0.98      | ~ v4_pre_topc(u1_struct_0(X0),X1)
% 4.04/0.98      | v1_borsuk_1(X0,X1)
% 4.04/0.98      | ~ v2_pre_topc(X1)
% 4.04/0.98      | ~ l1_pre_topc(X1) ),
% 4.04/0.98      inference(global_propositional_subsumption,
% 4.04/0.98                [status(thm)],
% 4.04/0.98                [c_15,c_19]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_304,plain,
% 4.04/0.98      ( v1_borsuk_1(X0,X1)
% 4.04/0.98      | ~ v4_pre_topc(u1_struct_0(X0),X1)
% 4.04/0.98      | ~ m1_pre_topc(X0,X1)
% 4.04/0.98      | ~ v2_pre_topc(X1)
% 4.04/0.98      | ~ l1_pre_topc(X1) ),
% 4.04/0.98      inference(renaming,[status(thm)],[c_303]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1174,plain,
% 4.04/0.98      ( v1_borsuk_1(X0,X1) = iProver_top
% 4.04/0.98      | v4_pre_topc(u1_struct_0(X0),X1) != iProver_top
% 4.04/0.98      | m1_pre_topc(X0,X1) != iProver_top
% 4.04/0.98      | v2_pre_topc(X1) != iProver_top
% 4.04/0.98      | l1_pre_topc(X1) != iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_2623,plain,
% 4.04/0.98      ( v1_borsuk_1(sK1,X0) = iProver_top
% 4.04/0.98      | v4_pre_topc(k2_struct_0(sK1),X0) != iProver_top
% 4.04/0.98      | m1_pre_topc(sK1,X0) != iProver_top
% 4.04/0.98      | v2_pre_topc(X0) != iProver_top
% 4.04/0.98      | l1_pre_topc(X0) != iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_2331,c_1174]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_15195,plain,
% 4.04/0.98      ( v1_borsuk_1(sK1,X0) = iProver_top
% 4.04/0.98      | v4_pre_topc(k2_struct_0(sK2),X0) != iProver_top
% 4.04/0.98      | m1_pre_topc(sK1,X0) != iProver_top
% 4.04/0.98      | v2_pre_topc(X0) != iProver_top
% 4.04/0.98      | l1_pre_topc(X0) != iProver_top ),
% 4.04/0.98      inference(demodulation,[status(thm)],[c_15186,c_2623]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_15352,plain,
% 4.04/0.98      ( v1_borsuk_1(sK1,sK0) = iProver_top
% 4.04/0.98      | v4_pre_topc(k2_struct_0(sK2),sK0) != iProver_top
% 4.04/0.98      | m1_pre_topc(sK1,sK0) != iProver_top
% 4.04/0.98      | v2_pre_topc(sK0) != iProver_top
% 4.04/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 4.04/0.98      inference(instantiation,[status(thm)],[c_15195]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_21,negated_conjecture,
% 4.04/0.98      ( m1_pre_topc(sK1,sK0) | m1_pre_topc(sK2,sK0) ),
% 4.04/0.98      inference(cnf_transformation,[],[f71]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1185,plain,
% 4.04/0.98      ( m1_pre_topc(sK1,sK0) = iProver_top
% 4.04/0.98      | m1_pre_topc(sK2,sK0) = iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_17,plain,
% 4.04/0.98      ( ~ m1_pre_topc(X0,X1)
% 4.04/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 4.04/0.98      | ~ v2_pre_topc(X0)
% 4.04/0.98      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 4.04/0.98      | ~ l1_pre_topc(X1)
% 4.04/0.98      | ~ l1_pre_topc(X0)
% 4.04/0.98      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 4.04/0.98      inference(cnf_transformation,[],[f78]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1189,plain,
% 4.04/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 4.04/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 4.04/0.98      | v2_pre_topc(X0) != iProver_top
% 4.04/0.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 4.04/0.98      | l1_pre_topc(X1) != iProver_top
% 4.04/0.98      | l1_pre_topc(X0) != iProver_top
% 4.04/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_4630,plain,
% 4.04/0.98      ( m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top
% 4.04/0.98      | m1_pre_topc(sK1,X0) != iProver_top
% 4.04/0.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 4.04/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.04/0.98      | l1_pre_topc(X0) != iProver_top
% 4.04/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 4.04/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_2331,c_1189]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_4671,plain,
% 4.04/0.98      ( m1_pre_topc(sK1,X0) != iProver_top
% 4.04/0.98      | m1_pre_topc(sK2,X0) = iProver_top
% 4.04/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.04/0.98      | v2_pre_topc(sK2) != iProver_top
% 4.04/0.98      | l1_pre_topc(X0) != iProver_top
% 4.04/0.98      | l1_pre_topc(sK1) != iProver_top
% 4.04/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 4.04/0.98      inference(light_normalisation,[status(thm)],[c_4630,c_2331,c_2621]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_4964,plain,
% 4.04/0.98      ( m1_pre_topc(sK1,X0) != iProver_top
% 4.04/0.98      | m1_pre_topc(sK2,X0) = iProver_top
% 4.04/0.98      | l1_pre_topc(X0) != iProver_top ),
% 4.04/0.98      inference(global_propositional_subsumption,
% 4.04/0.98                [status(thm)],
% 4.04/0.98                [c_4671,c_34,c_35,c_36,c_37]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_4973,plain,
% 4.04/0.98      ( m1_pre_topc(sK2,sK0) = iProver_top
% 4.04/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_1185,c_4964]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_18,plain,
% 4.04/0.98      ( m1_pre_topc(X0,X1)
% 4.04/0.98      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 4.04/0.98      | ~ v2_pre_topc(X0)
% 4.04/0.98      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 4.04/0.98      | ~ l1_pre_topc(X1)
% 4.04/0.98      | ~ l1_pre_topc(X0)
% 4.04/0.98      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 4.04/0.98      inference(cnf_transformation,[],[f79]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_1188,plain,
% 4.04/0.98      ( m1_pre_topc(X0,X1) = iProver_top
% 4.04/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 4.04/0.98      | v2_pre_topc(X0) != iProver_top
% 4.04/0.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 4.04/0.98      | l1_pre_topc(X1) != iProver_top
% 4.04/0.98      | l1_pre_topc(X0) != iProver_top
% 4.04/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_4327,plain,
% 4.04/0.98      ( m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 4.04/0.98      | m1_pre_topc(sK1,X0) = iProver_top
% 4.04/0.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 4.04/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.04/0.98      | l1_pre_topc(X0) != iProver_top
% 4.04/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 4.04/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_2331,c_1188]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_4367,plain,
% 4.04/0.98      ( m1_pre_topc(sK1,X0) = iProver_top
% 4.04/0.98      | m1_pre_topc(sK2,X0) != iProver_top
% 4.04/0.98      | v2_pre_topc(sK1) != iProver_top
% 4.04/0.98      | v2_pre_topc(sK2) != iProver_top
% 4.04/0.98      | l1_pre_topc(X0) != iProver_top
% 4.04/0.98      | l1_pre_topc(sK1) != iProver_top
% 4.04/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 4.04/0.98      inference(light_normalisation,[status(thm)],[c_4327,c_2331,c_2621]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_4867,plain,
% 4.04/0.98      ( m1_pre_topc(sK1,X0) = iProver_top
% 4.04/0.98      | m1_pre_topc(sK2,X0) != iProver_top
% 4.04/0.98      | l1_pre_topc(X0) != iProver_top ),
% 4.04/0.98      inference(global_propositional_subsumption,
% 4.04/0.98                [status(thm)],
% 4.04/0.98                [c_4367,c_34,c_35,c_36,c_37]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_4870,plain,
% 4.04/0.98      ( m1_pre_topc(sK1,sK0) = iProver_top
% 4.04/0.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 4.04/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 4.04/0.98      inference(instantiation,[status(thm)],[c_4867]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_2593,plain,
% 4.04/0.98      ( v1_borsuk_1(sK2,X0) = iProver_top
% 4.04/0.98      | v4_pre_topc(k2_struct_0(sK2),X0) != iProver_top
% 4.04/0.98      | m1_pre_topc(sK2,X0) != iProver_top
% 4.04/0.98      | v2_pre_topc(X0) != iProver_top
% 4.04/0.98      | l1_pre_topc(X0) != iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_2330,c_1174]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_2618,plain,
% 4.04/0.98      ( v1_borsuk_1(sK2,sK0) = iProver_top
% 4.04/0.98      | v4_pre_topc(k2_struct_0(sK2),sK0) != iProver_top
% 4.04/0.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 4.04/0.98      | v2_pre_topc(sK0) != iProver_top
% 4.04/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 4.04/0.98      inference(instantiation,[status(thm)],[c_2593]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_2592,plain,
% 4.04/0.98      ( v1_borsuk_1(sK2,X0) != iProver_top
% 4.04/0.98      | v4_pre_topc(k2_struct_0(sK2),X0) = iProver_top
% 4.04/0.98      | m1_pre_topc(sK2,X0) != iProver_top
% 4.04/0.98      | v2_pre_topc(X0) != iProver_top
% 4.04/0.98      | l1_pre_topc(X0) != iProver_top ),
% 4.04/0.98      inference(superposition,[status(thm)],[c_2330,c_1175]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_2615,plain,
% 4.04/0.98      ( v1_borsuk_1(sK2,sK0) != iProver_top
% 4.04/0.98      | v4_pre_topc(k2_struct_0(sK2),sK0) = iProver_top
% 4.04/0.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 4.04/0.98      | v2_pre_topc(sK0) != iProver_top
% 4.04/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 4.04/0.98      inference(instantiation,[status(thm)],[c_2592]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_20,negated_conjecture,
% 4.04/0.98      ( ~ v1_borsuk_1(sK1,sK0)
% 4.04/0.98      | ~ v1_borsuk_1(sK2,sK0)
% 4.04/0.98      | ~ m1_pre_topc(sK1,sK0)
% 4.04/0.98      | ~ m1_pre_topc(sK2,sK0) ),
% 4.04/0.98      inference(cnf_transformation,[],[f72]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_42,plain,
% 4.04/0.98      ( v1_borsuk_1(sK1,sK0) != iProver_top
% 4.04/0.98      | v1_borsuk_1(sK2,sK0) != iProver_top
% 4.04/0.98      | m1_pre_topc(sK1,sK0) != iProver_top
% 4.04/0.98      | m1_pre_topc(sK2,sK0) != iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_24,negated_conjecture,
% 4.04/0.98      ( v1_borsuk_1(sK1,sK0) | v1_borsuk_1(sK2,sK0) ),
% 4.04/0.98      inference(cnf_transformation,[],[f68]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_38,plain,
% 4.04/0.98      ( v1_borsuk_1(sK1,sK0) = iProver_top
% 4.04/0.98      | v1_borsuk_1(sK2,sK0) = iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_30,negated_conjecture,
% 4.04/0.98      ( l1_pre_topc(sK0) ),
% 4.04/0.98      inference(cnf_transformation,[],[f62]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_33,plain,
% 4.04/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_31,negated_conjecture,
% 4.04/0.98      ( v2_pre_topc(sK0) ),
% 4.04/0.98      inference(cnf_transformation,[],[f61]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(c_32,plain,
% 4.04/0.98      ( v2_pre_topc(sK0) = iProver_top ),
% 4.04/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.04/0.98  
% 4.04/0.98  cnf(contradiction,plain,
% 4.04/0.98      ( $false ),
% 4.04/0.98      inference(minisat,
% 4.04/0.98                [status(thm)],
% 4.04/0.98                [c_15358,c_15352,c_4973,c_4870,c_2618,c_2615,c_42,c_38,
% 4.04/0.98                 c_33,c_32]) ).
% 4.04/0.98  
% 4.04/0.98  
% 4.04/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.04/0.98  
% 4.04/0.98  ------                               Statistics
% 4.04/0.98  
% 4.04/0.98  ------ Selected
% 4.04/0.98  
% 4.04/0.98  total_time:                             0.492
% 4.04/0.98  
%------------------------------------------------------------------------------
