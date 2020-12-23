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
% DateTime   : Thu Dec  3 12:18:09 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  195 (32047 expanded)
%              Number of clauses        :  137 (11442 expanded)
%              Number of leaves         :   14 (5881 expanded)
%              Depth                    :   29
%              Number of atoms          :  673 (152202 expanded)
%              Number of equality atoms :  320 (21321 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
     => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
          | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
          | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v2_compts_1(sK1,X0) )
        & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(sK1,X0) ) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_compts_1(X1,X0) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
                & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v2_compts_1(X1,X0) ) ) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v2_compts_1(X1,sK0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
              & v2_compts_1(X1,sK0) ) ) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_compts_1(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v2_compts_1(sK1,sK0) ) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).

fof(f56,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
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

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( ( v2_compts_1(X1,X0)
                  | ~ v1_compts_1(k1_pre_topc(X0,X1)) )
                & ( v1_compts_1(k1_pre_topc(X0,X1))
                  | ~ v2_compts_1(X1,X0) ) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( ( v2_compts_1(X1,X0)
                  | ~ v1_compts_1(k1_pre_topc(X0,X1)) )
                & ( v1_compts_1(k1_pre_topc(X0,X1))
                  | ~ v2_compts_1(X1,X0) ) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X0,X1))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 = X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
             => ( X1 = X2
               => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
      | X1 != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X2,X0] :
      ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X2)),u1_pre_topc(k1_pre_topc(X0,X2))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f43,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | ~ v1_compts_1(k1_pre_topc(X0,X1))
      | k1_xboole_0 = X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | ~ v1_compts_1(k1_pre_topc(X0,X1))
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X0] :
      ( v2_compts_1(k1_xboole_0,X0)
      | ~ v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X0,X1))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X0] :
      ( v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
      | ~ v2_compts_1(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f47])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1148,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_257,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | l1_pre_topc(X3)
    | X2 != X1
    | k1_pre_topc(X1,X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_5])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_1142,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_258])).

cnf(c_1436,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_1142])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_24,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_55,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_57,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1344,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1345,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1344])).

cnf(c_1347,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1345])).

cnf(c_1767,plain,
    ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1436,c_24,c_57,c_1347])).

cnf(c_1768,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1767])).

cnf(c_1159,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1162,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1620,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1162])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1163,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1914,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1620,c_1163])).

cnf(c_1358,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1359,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1358])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1161,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1528,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1161])).

cnf(c_2542,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1914,c_1359,c_1528,c_1620])).

cnf(c_2543,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2542])).

cnf(c_2552,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))),u1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))))) = g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1768,c_2543])).

cnf(c_13,plain,
    ( ~ v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_compts_1(k1_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1152,plain,
    ( k1_xboole_0 = X0
    | v2_compts_1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_compts_1(k1_pre_topc(X1,X0)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3614,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))),u1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))))) = g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))
    | sK1 = k1_xboole_0
    | v2_compts_1(sK1,sK0) != iProver_top
    | v1_compts_1(k1_pre_topc(sK0,sK1)) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2552,c_1152])).

cnf(c_1144,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2550,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(superposition,[status(thm)],[c_1144,c_2543])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1155,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2667,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2550,c_1155])).

cnf(c_2888,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0)
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2667])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_56,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_315,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != X1
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_316,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_318,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_1346,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_1344])).

cnf(c_1803,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | X1 = u1_struct_0(sK0)
    | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK0),X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2159,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | X0 = u1_struct_0(sK0)
    | g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(instantiation,[status(thm)],[c_1803])).

cnf(c_2656,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2159])).

cnf(c_3743,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2888,c_22,c_21,c_56,c_318,c_1346,c_2656])).

cnf(c_3751,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3743,c_1148])).

cnf(c_16,negated_conjecture,
    ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1149,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_compts_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3753,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_compts_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3743,c_1149])).

cnf(c_3766,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_compts_1(sK1,sK0) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3751,c_3753])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1154,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3814,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,X0)),u1_pre_topc(k1_pre_topc(sK0,X0))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3743,c_1154])).

cnf(c_5618,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,X0)),u1_pre_topc(k1_pre_topc(sK0,X0))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3814,c_24])).

cnf(c_5619,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,X0)),u1_pre_topc(k1_pre_topc(sK0,X0))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5618])).

cnf(c_5626,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    inference(superposition,[status(thm)],[c_3751,c_5619])).

cnf(c_3929,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3751,c_1142])).

cnf(c_1374,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_258])).

cnf(c_1375,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1374])).

cnf(c_4065,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3929,c_24,c_1375,c_3751])).

cnf(c_4071,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(sK0,sK1)
    | v1_pre_topc(k1_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4065,c_1163])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1371,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1372,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_pre_topc(k1_pre_topc(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1371])).

cnf(c_1412,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
    | g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1413,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(sK0,sK1)
    | l1_pre_topc(k1_pre_topc(sK0,sK1)) != iProver_top
    | v1_pre_topc(k1_pre_topc(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1412])).

cnf(c_4283,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4071,c_24,c_1372,c_1375,c_1413,c_3751])).

cnf(c_5627,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_5626,c_4283])).

cnf(c_18,negated_conjecture,
    ( v2_compts_1(sK1,sK0)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1147,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2422,plain,
    ( sK1 = k1_xboole_0
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_compts_1(sK1,sK0) = iProver_top
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1147,c_1152])).

cnf(c_23,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_20,negated_conjecture,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_25,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_compts_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_52,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_54,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_2809,plain,
    ( sK1 = k1_xboole_0
    | v2_compts_1(sK1,sK0) = iProver_top
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2422,c_23,c_24,c_25,c_54,c_57,c_1347])).

cnf(c_5891,plain,
    ( sK1 = k1_xboole_0
    | v2_compts_1(sK1,sK0) = iProver_top
    | v1_compts_1(k1_pre_topc(sK0,sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5627,c_2809])).

cnf(c_1160,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_pre_topc(k1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2046,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_1160])).

cnf(c_2151,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2046,c_24,c_57,c_1347])).

cnf(c_1773,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1768,c_1163])).

cnf(c_2157,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2151,c_1773])).

cnf(c_2423,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | sK1 = k1_xboole_0
    | v2_compts_1(sK1,sK0) != iProver_top
    | v1_compts_1(k1_pre_topc(sK0,sK1)) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2157,c_1152])).

cnf(c_3927,plain,
    ( sK1 = k1_xboole_0
    | v2_compts_1(sK1,sK0) != iProver_top
    | v1_compts_1(k1_pre_topc(sK0,sK1)) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3751,c_1152])).

cnf(c_4212,plain,
    ( sK1 = k1_xboole_0
    | v2_compts_1(sK1,sK0) != iProver_top
    | v1_compts_1(k1_pre_topc(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2423,c_23,c_24,c_3927])).

cnf(c_6063,plain,
    ( sK1 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5891,c_4212])).

cnf(c_12,plain,
    ( v2_compts_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_compts_1(k1_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1153,plain,
    ( k1_xboole_0 = X0
    | v2_compts_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_compts_1(k1_pre_topc(X1,X0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3926,plain,
    ( sK1 = k1_xboole_0
    | v2_compts_1(sK1,sK0) = iProver_top
    | v1_compts_1(k1_pre_topc(sK0,sK1)) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3751,c_1153])).

cnf(c_1419,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1420,plain,
    ( k1_xboole_0 = sK1
    | v2_compts_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v1_compts_1(k1_pre_topc(sK0,sK1)) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1419])).

cnf(c_716,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1463,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_716])).

cnf(c_717,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_1586,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_1842,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1586])).

cnf(c_4646,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1842])).

cnf(c_4711,plain,
    ( sK1 = k1_xboole_0
    | v2_compts_1(sK1,sK0) = iProver_top
    | v1_compts_1(k1_pre_topc(sK0,sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3926,c_23,c_24,c_1420,c_1463,c_3751,c_4646])).

cnf(c_6069,plain,
    ( sK1 = k1_xboole_0
    | v2_compts_1(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6063,c_4711])).

cnf(c_3810,plain,
    ( k1_xboole_0 = X0
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3743,c_1153])).

cnf(c_6298,plain,
    ( k1_xboole_0 = X0
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3810,c_23,c_24,c_54,c_57,c_1347])).

cnf(c_6309,plain,
    ( sK1 = k1_xboole_0
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v1_compts_1(k1_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5627,c_6298])).

cnf(c_6503,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3614,c_3751,c_3766,c_6063,c_6069,c_6309])).

cnf(c_6506,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6503,c_5627])).

cnf(c_14,plain,
    ( v2_compts_1(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1151,plain,
    ( v2_compts_1(k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3804,plain,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3743,c_1151])).

cnf(c_5879,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3804,c_24,c_57,c_1347])).

cnf(c_5880,plain,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5879])).

cnf(c_7566,plain,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6506,c_5880])).

cnf(c_15,plain,
    ( ~ v2_compts_1(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1150,plain,
    ( v2_compts_1(k1_xboole_0,X0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3806,plain,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3743,c_1150])).

cnf(c_6284,plain,
    ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3806,c_24,c_57,c_1347])).

cnf(c_6285,plain,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6284])).

cnf(c_7565,plain,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6506,c_6285])).

cnf(c_6515,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6503,c_3751])).

cnf(c_6805,plain,
    ( v2_compts_1(k1_xboole_0,sK0) != iProver_top
    | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6515,c_1150])).

cnf(c_6940,plain,
    ( v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) = iProver_top
    | v2_compts_1(k1_xboole_0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6805,c_24])).

cnf(c_6941,plain,
    ( v2_compts_1(k1_xboole_0,sK0) != iProver_top
    | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6940])).

cnf(c_6804,plain,
    ( v2_compts_1(k1_xboole_0,sK0) = iProver_top
    | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6515,c_1151])).

cnf(c_6827,plain,
    ( v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) != iProver_top
    | v2_compts_1(k1_xboole_0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6804,c_24])).

cnf(c_6828,plain,
    ( v2_compts_1(k1_xboole_0,sK0) = iProver_top
    | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6827])).

cnf(c_1145,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_compts_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6517,plain,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_compts_1(k1_xboole_0,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6503,c_1145])).

cnf(c_6509,plain,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_compts_1(k1_xboole_0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6503,c_3766])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7566,c_7565,c_6941,c_6828,c_6517,c_6515,c_6509])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.17/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/0.98  
% 3.17/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.17/0.98  
% 3.17/0.98  ------  iProver source info
% 3.17/0.98  
% 3.17/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.17/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.17/0.98  git: non_committed_changes: false
% 3.17/0.98  git: last_make_outside_of_git: false
% 3.17/0.98  
% 3.17/0.98  ------ 
% 3.17/0.98  
% 3.17/0.98  ------ Input Options
% 3.17/0.98  
% 3.17/0.98  --out_options                           all
% 3.17/0.98  --tptp_safe_out                         true
% 3.17/0.98  --problem_path                          ""
% 3.17/0.98  --include_path                          ""
% 3.17/0.98  --clausifier                            res/vclausify_rel
% 3.17/0.98  --clausifier_options                    --mode clausify
% 3.17/0.98  --stdin                                 false
% 3.17/0.98  --stats_out                             all
% 3.17/0.98  
% 3.17/0.98  ------ General Options
% 3.17/0.98  
% 3.17/0.98  --fof                                   false
% 3.17/0.98  --time_out_real                         305.
% 3.17/0.98  --time_out_virtual                      -1.
% 3.17/0.98  --symbol_type_check                     false
% 3.17/0.98  --clausify_out                          false
% 3.17/0.98  --sig_cnt_out                           false
% 3.17/0.98  --trig_cnt_out                          false
% 3.17/0.98  --trig_cnt_out_tolerance                1.
% 3.17/0.98  --trig_cnt_out_sk_spl                   false
% 3.17/0.98  --abstr_cl_out                          false
% 3.17/0.98  
% 3.17/0.98  ------ Global Options
% 3.17/0.98  
% 3.17/0.98  --schedule                              default
% 3.17/0.98  --add_important_lit                     false
% 3.17/0.98  --prop_solver_per_cl                    1000
% 3.17/0.98  --min_unsat_core                        false
% 3.17/0.98  --soft_assumptions                      false
% 3.17/0.98  --soft_lemma_size                       3
% 3.17/0.98  --prop_impl_unit_size                   0
% 3.17/0.98  --prop_impl_unit                        []
% 3.17/0.98  --share_sel_clauses                     true
% 3.17/0.98  --reset_solvers                         false
% 3.17/0.98  --bc_imp_inh                            [conj_cone]
% 3.17/0.98  --conj_cone_tolerance                   3.
% 3.17/0.98  --extra_neg_conj                        none
% 3.17/0.98  --large_theory_mode                     true
% 3.17/0.98  --prolific_symb_bound                   200
% 3.17/0.98  --lt_threshold                          2000
% 3.17/0.98  --clause_weak_htbl                      true
% 3.17/0.98  --gc_record_bc_elim                     false
% 3.17/0.98  
% 3.17/0.98  ------ Preprocessing Options
% 3.17/0.98  
% 3.17/0.98  --preprocessing_flag                    true
% 3.17/0.98  --time_out_prep_mult                    0.1
% 3.17/0.98  --splitting_mode                        input
% 3.17/0.98  --splitting_grd                         true
% 3.17/0.98  --splitting_cvd                         false
% 3.17/0.98  --splitting_cvd_svl                     false
% 3.17/0.98  --splitting_nvd                         32
% 3.17/0.98  --sub_typing                            true
% 3.17/0.98  --prep_gs_sim                           true
% 3.17/0.98  --prep_unflatten                        true
% 3.17/0.98  --prep_res_sim                          true
% 3.17/0.98  --prep_upred                            true
% 3.17/0.98  --prep_sem_filter                       exhaustive
% 3.17/0.98  --prep_sem_filter_out                   false
% 3.17/0.98  --pred_elim                             true
% 3.17/0.98  --res_sim_input                         true
% 3.17/0.98  --eq_ax_congr_red                       true
% 3.17/0.98  --pure_diseq_elim                       true
% 3.17/0.98  --brand_transform                       false
% 3.17/0.98  --non_eq_to_eq                          false
% 3.17/0.98  --prep_def_merge                        true
% 3.17/0.98  --prep_def_merge_prop_impl              false
% 3.17/0.98  --prep_def_merge_mbd                    true
% 3.17/0.98  --prep_def_merge_tr_red                 false
% 3.17/0.98  --prep_def_merge_tr_cl                  false
% 3.17/0.98  --smt_preprocessing                     true
% 3.17/0.98  --smt_ac_axioms                         fast
% 3.17/0.98  --preprocessed_out                      false
% 3.17/0.98  --preprocessed_stats                    false
% 3.17/0.98  
% 3.17/0.98  ------ Abstraction refinement Options
% 3.17/0.98  
% 3.17/0.98  --abstr_ref                             []
% 3.17/0.98  --abstr_ref_prep                        false
% 3.17/0.98  --abstr_ref_until_sat                   false
% 3.17/0.98  --abstr_ref_sig_restrict                funpre
% 3.17/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/0.98  --abstr_ref_under                       []
% 3.17/0.98  
% 3.17/0.98  ------ SAT Options
% 3.17/0.98  
% 3.17/0.98  --sat_mode                              false
% 3.17/0.98  --sat_fm_restart_options                ""
% 3.17/0.98  --sat_gr_def                            false
% 3.17/0.98  --sat_epr_types                         true
% 3.17/0.98  --sat_non_cyclic_types                  false
% 3.17/0.98  --sat_finite_models                     false
% 3.17/0.98  --sat_fm_lemmas                         false
% 3.17/0.98  --sat_fm_prep                           false
% 3.17/0.98  --sat_fm_uc_incr                        true
% 3.17/0.98  --sat_out_model                         small
% 3.17/0.98  --sat_out_clauses                       false
% 3.17/0.98  
% 3.17/0.98  ------ QBF Options
% 3.17/0.98  
% 3.17/0.98  --qbf_mode                              false
% 3.17/0.98  --qbf_elim_univ                         false
% 3.17/0.98  --qbf_dom_inst                          none
% 3.17/0.98  --qbf_dom_pre_inst                      false
% 3.17/0.98  --qbf_sk_in                             false
% 3.17/0.98  --qbf_pred_elim                         true
% 3.17/0.98  --qbf_split                             512
% 3.17/0.98  
% 3.17/0.98  ------ BMC1 Options
% 3.17/0.98  
% 3.17/0.98  --bmc1_incremental                      false
% 3.17/0.98  --bmc1_axioms                           reachable_all
% 3.17/0.98  --bmc1_min_bound                        0
% 3.17/0.98  --bmc1_max_bound                        -1
% 3.17/0.98  --bmc1_max_bound_default                -1
% 3.17/0.98  --bmc1_symbol_reachability              true
% 3.17/0.98  --bmc1_property_lemmas                  false
% 3.17/0.98  --bmc1_k_induction                      false
% 3.17/0.98  --bmc1_non_equiv_states                 false
% 3.17/0.98  --bmc1_deadlock                         false
% 3.17/0.98  --bmc1_ucm                              false
% 3.17/0.98  --bmc1_add_unsat_core                   none
% 3.17/0.98  --bmc1_unsat_core_children              false
% 3.17/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/0.98  --bmc1_out_stat                         full
% 3.17/0.98  --bmc1_ground_init                      false
% 3.17/0.98  --bmc1_pre_inst_next_state              false
% 3.17/0.98  --bmc1_pre_inst_state                   false
% 3.17/0.98  --bmc1_pre_inst_reach_state             false
% 3.17/0.98  --bmc1_out_unsat_core                   false
% 3.17/0.98  --bmc1_aig_witness_out                  false
% 3.17/0.98  --bmc1_verbose                          false
% 3.17/0.98  --bmc1_dump_clauses_tptp                false
% 3.17/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.17/0.98  --bmc1_dump_file                        -
% 3.17/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.17/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.17/0.98  --bmc1_ucm_extend_mode                  1
% 3.17/0.98  --bmc1_ucm_init_mode                    2
% 3.17/0.98  --bmc1_ucm_cone_mode                    none
% 3.17/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.17/0.98  --bmc1_ucm_relax_model                  4
% 3.17/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.17/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/0.98  --bmc1_ucm_layered_model                none
% 3.17/0.98  --bmc1_ucm_max_lemma_size               10
% 3.17/0.98  
% 3.17/0.98  ------ AIG Options
% 3.17/0.98  
% 3.17/0.98  --aig_mode                              false
% 3.17/0.98  
% 3.17/0.98  ------ Instantiation Options
% 3.17/0.98  
% 3.17/0.98  --instantiation_flag                    true
% 3.17/0.98  --inst_sos_flag                         false
% 3.17/0.98  --inst_sos_phase                        true
% 3.17/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/0.98  --inst_lit_sel_side                     num_symb
% 3.17/0.98  --inst_solver_per_active                1400
% 3.17/0.98  --inst_solver_calls_frac                1.
% 3.17/0.98  --inst_passive_queue_type               priority_queues
% 3.17/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/0.98  --inst_passive_queues_freq              [25;2]
% 3.17/0.98  --inst_dismatching                      true
% 3.17/0.98  --inst_eager_unprocessed_to_passive     true
% 3.17/0.98  --inst_prop_sim_given                   true
% 3.17/0.98  --inst_prop_sim_new                     false
% 3.17/0.98  --inst_subs_new                         false
% 3.17/0.98  --inst_eq_res_simp                      false
% 3.17/0.98  --inst_subs_given                       false
% 3.17/0.98  --inst_orphan_elimination               true
% 3.17/0.98  --inst_learning_loop_flag               true
% 3.17/0.98  --inst_learning_start                   3000
% 3.17/0.98  --inst_learning_factor                  2
% 3.17/0.98  --inst_start_prop_sim_after_learn       3
% 3.17/0.98  --inst_sel_renew                        solver
% 3.17/0.98  --inst_lit_activity_flag                true
% 3.17/0.98  --inst_restr_to_given                   false
% 3.17/0.98  --inst_activity_threshold               500
% 3.17/0.98  --inst_out_proof                        true
% 3.17/0.98  
% 3.17/0.98  ------ Resolution Options
% 3.17/0.98  
% 3.17/0.98  --resolution_flag                       true
% 3.17/0.98  --res_lit_sel                           adaptive
% 3.17/0.98  --res_lit_sel_side                      none
% 3.17/0.98  --res_ordering                          kbo
% 3.17/0.98  --res_to_prop_solver                    active
% 3.17/0.98  --res_prop_simpl_new                    false
% 3.17/0.98  --res_prop_simpl_given                  true
% 3.17/0.98  --res_passive_queue_type                priority_queues
% 3.17/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/0.98  --res_passive_queues_freq               [15;5]
% 3.17/0.98  --res_forward_subs                      full
% 3.17/0.98  --res_backward_subs                     full
% 3.17/0.98  --res_forward_subs_resolution           true
% 3.17/0.98  --res_backward_subs_resolution          true
% 3.17/0.98  --res_orphan_elimination                true
% 3.17/0.98  --res_time_limit                        2.
% 3.17/0.98  --res_out_proof                         true
% 3.17/0.98  
% 3.17/0.98  ------ Superposition Options
% 3.17/0.98  
% 3.17/0.98  --superposition_flag                    true
% 3.17/0.98  --sup_passive_queue_type                priority_queues
% 3.17/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.17/0.98  --demod_completeness_check              fast
% 3.17/0.98  --demod_use_ground                      true
% 3.17/0.98  --sup_to_prop_solver                    passive
% 3.17/0.98  --sup_prop_simpl_new                    true
% 3.17/0.98  --sup_prop_simpl_given                  true
% 3.17/0.98  --sup_fun_splitting                     false
% 3.17/0.98  --sup_smt_interval                      50000
% 3.17/0.98  
% 3.17/0.98  ------ Superposition Simplification Setup
% 3.17/0.98  
% 3.17/0.98  --sup_indices_passive                   []
% 3.17/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.98  --sup_full_bw                           [BwDemod]
% 3.17/0.98  --sup_immed_triv                        [TrivRules]
% 3.17/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.98  --sup_immed_bw_main                     []
% 3.17/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.98  
% 3.17/0.98  ------ Combination Options
% 3.17/0.98  
% 3.17/0.98  --comb_res_mult                         3
% 3.17/0.98  --comb_sup_mult                         2
% 3.17/0.98  --comb_inst_mult                        10
% 3.17/0.98  
% 3.17/0.98  ------ Debug Options
% 3.17/0.98  
% 3.17/0.98  --dbg_backtrace                         false
% 3.17/0.98  --dbg_dump_prop_clauses                 false
% 3.17/0.98  --dbg_dump_prop_clauses_file            -
% 3.17/0.98  --dbg_out_stat                          false
% 3.17/0.98  ------ Parsing...
% 3.17/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.17/0.98  
% 3.17/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.17/0.98  
% 3.17/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.17/0.98  
% 3.17/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.17/0.98  ------ Proving...
% 3.17/0.98  ------ Problem Properties 
% 3.17/0.98  
% 3.17/0.98  
% 3.17/0.98  clauses                                 22
% 3.17/0.98  conjectures                             7
% 3.17/0.98  EPR                                     2
% 3.17/0.98  Horn                                    16
% 3.17/0.98  unary                                   2
% 3.17/0.98  binary                                  7
% 3.17/0.98  lits                                    65
% 3.17/0.98  lits eq                                 8
% 3.17/0.98  fd_pure                                 0
% 3.17/0.98  fd_pseudo                               0
% 3.17/0.98  fd_cond                                 2
% 3.17/0.98  fd_pseudo_cond                          2
% 3.17/0.98  AC symbols                              0
% 3.17/0.98  
% 3.17/0.98  ------ Schedule dynamic 5 is on 
% 3.17/0.98  
% 3.17/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.17/0.98  
% 3.17/0.98  
% 3.17/0.98  ------ 
% 3.17/0.98  Current options:
% 3.17/0.98  ------ 
% 3.17/0.98  
% 3.17/0.98  ------ Input Options
% 3.17/0.98  
% 3.17/0.98  --out_options                           all
% 3.17/0.98  --tptp_safe_out                         true
% 3.17/0.98  --problem_path                          ""
% 3.17/0.98  --include_path                          ""
% 3.17/0.98  --clausifier                            res/vclausify_rel
% 3.17/0.98  --clausifier_options                    --mode clausify
% 3.17/0.98  --stdin                                 false
% 3.17/0.98  --stats_out                             all
% 3.17/0.98  
% 3.17/0.98  ------ General Options
% 3.17/0.98  
% 3.17/0.98  --fof                                   false
% 3.17/0.98  --time_out_real                         305.
% 3.17/0.98  --time_out_virtual                      -1.
% 3.17/0.98  --symbol_type_check                     false
% 3.17/0.98  --clausify_out                          false
% 3.17/0.98  --sig_cnt_out                           false
% 3.17/0.98  --trig_cnt_out                          false
% 3.17/0.98  --trig_cnt_out_tolerance                1.
% 3.17/0.98  --trig_cnt_out_sk_spl                   false
% 3.17/0.98  --abstr_cl_out                          false
% 3.17/0.98  
% 3.17/0.98  ------ Global Options
% 3.17/0.98  
% 3.17/0.98  --schedule                              default
% 3.17/0.98  --add_important_lit                     false
% 3.17/0.98  --prop_solver_per_cl                    1000
% 3.17/0.98  --min_unsat_core                        false
% 3.17/0.98  --soft_assumptions                      false
% 3.17/0.98  --soft_lemma_size                       3
% 3.17/0.98  --prop_impl_unit_size                   0
% 3.17/0.98  --prop_impl_unit                        []
% 3.17/0.98  --share_sel_clauses                     true
% 3.17/0.98  --reset_solvers                         false
% 3.17/0.98  --bc_imp_inh                            [conj_cone]
% 3.17/0.98  --conj_cone_tolerance                   3.
% 3.17/0.98  --extra_neg_conj                        none
% 3.17/0.98  --large_theory_mode                     true
% 3.17/0.98  --prolific_symb_bound                   200
% 3.17/0.98  --lt_threshold                          2000
% 3.17/0.98  --clause_weak_htbl                      true
% 3.17/0.98  --gc_record_bc_elim                     false
% 3.17/0.98  
% 3.17/0.98  ------ Preprocessing Options
% 3.17/0.98  
% 3.17/0.98  --preprocessing_flag                    true
% 3.17/0.98  --time_out_prep_mult                    0.1
% 3.17/0.98  --splitting_mode                        input
% 3.17/0.98  --splitting_grd                         true
% 3.17/0.98  --splitting_cvd                         false
% 3.17/0.98  --splitting_cvd_svl                     false
% 3.17/0.98  --splitting_nvd                         32
% 3.17/0.98  --sub_typing                            true
% 3.17/0.98  --prep_gs_sim                           true
% 3.17/0.98  --prep_unflatten                        true
% 3.17/0.98  --prep_res_sim                          true
% 3.17/0.98  --prep_upred                            true
% 3.17/0.98  --prep_sem_filter                       exhaustive
% 3.17/0.98  --prep_sem_filter_out                   false
% 3.17/0.98  --pred_elim                             true
% 3.17/0.98  --res_sim_input                         true
% 3.17/0.98  --eq_ax_congr_red                       true
% 3.17/0.98  --pure_diseq_elim                       true
% 3.17/0.98  --brand_transform                       false
% 3.17/0.98  --non_eq_to_eq                          false
% 3.17/0.98  --prep_def_merge                        true
% 3.17/0.98  --prep_def_merge_prop_impl              false
% 3.17/0.98  --prep_def_merge_mbd                    true
% 3.17/0.98  --prep_def_merge_tr_red                 false
% 3.17/0.98  --prep_def_merge_tr_cl                  false
% 3.17/0.98  --smt_preprocessing                     true
% 3.17/0.98  --smt_ac_axioms                         fast
% 3.17/0.98  --preprocessed_out                      false
% 3.17/0.98  --preprocessed_stats                    false
% 3.17/0.98  
% 3.17/0.98  ------ Abstraction refinement Options
% 3.17/0.98  
% 3.17/0.98  --abstr_ref                             []
% 3.17/0.98  --abstr_ref_prep                        false
% 3.17/0.98  --abstr_ref_until_sat                   false
% 3.17/0.98  --abstr_ref_sig_restrict                funpre
% 3.17/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/0.98  --abstr_ref_under                       []
% 3.17/0.98  
% 3.17/0.98  ------ SAT Options
% 3.17/0.98  
% 3.17/0.98  --sat_mode                              false
% 3.17/0.98  --sat_fm_restart_options                ""
% 3.17/0.98  --sat_gr_def                            false
% 3.17/0.98  --sat_epr_types                         true
% 3.17/0.98  --sat_non_cyclic_types                  false
% 3.17/0.98  --sat_finite_models                     false
% 3.17/0.98  --sat_fm_lemmas                         false
% 3.17/0.98  --sat_fm_prep                           false
% 3.17/0.98  --sat_fm_uc_incr                        true
% 3.17/0.98  --sat_out_model                         small
% 3.17/0.98  --sat_out_clauses                       false
% 3.17/0.98  
% 3.17/0.98  ------ QBF Options
% 3.17/0.98  
% 3.17/0.98  --qbf_mode                              false
% 3.17/0.98  --qbf_elim_univ                         false
% 3.17/0.98  --qbf_dom_inst                          none
% 3.17/0.98  --qbf_dom_pre_inst                      false
% 3.17/0.98  --qbf_sk_in                             false
% 3.17/0.98  --qbf_pred_elim                         true
% 3.17/0.98  --qbf_split                             512
% 3.17/0.98  
% 3.17/0.98  ------ BMC1 Options
% 3.17/0.98  
% 3.17/0.98  --bmc1_incremental                      false
% 3.17/0.98  --bmc1_axioms                           reachable_all
% 3.17/0.98  --bmc1_min_bound                        0
% 3.17/0.98  --bmc1_max_bound                        -1
% 3.17/0.98  --bmc1_max_bound_default                -1
% 3.17/0.98  --bmc1_symbol_reachability              true
% 3.17/0.98  --bmc1_property_lemmas                  false
% 3.17/0.98  --bmc1_k_induction                      false
% 3.17/0.98  --bmc1_non_equiv_states                 false
% 3.17/0.98  --bmc1_deadlock                         false
% 3.17/0.98  --bmc1_ucm                              false
% 3.17/0.98  --bmc1_add_unsat_core                   none
% 3.17/0.98  --bmc1_unsat_core_children              false
% 3.17/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/0.98  --bmc1_out_stat                         full
% 3.17/0.98  --bmc1_ground_init                      false
% 3.17/0.98  --bmc1_pre_inst_next_state              false
% 3.17/0.98  --bmc1_pre_inst_state                   false
% 3.17/0.98  --bmc1_pre_inst_reach_state             false
% 3.17/0.98  --bmc1_out_unsat_core                   false
% 3.17/0.98  --bmc1_aig_witness_out                  false
% 3.17/0.98  --bmc1_verbose                          false
% 3.17/0.98  --bmc1_dump_clauses_tptp                false
% 3.17/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.17/0.98  --bmc1_dump_file                        -
% 3.17/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.17/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.17/0.98  --bmc1_ucm_extend_mode                  1
% 3.17/0.98  --bmc1_ucm_init_mode                    2
% 3.17/0.98  --bmc1_ucm_cone_mode                    none
% 3.17/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.17/0.98  --bmc1_ucm_relax_model                  4
% 3.17/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.17/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/0.98  --bmc1_ucm_layered_model                none
% 3.17/0.98  --bmc1_ucm_max_lemma_size               10
% 3.17/0.98  
% 3.17/0.98  ------ AIG Options
% 3.17/0.98  
% 3.17/0.98  --aig_mode                              false
% 3.17/0.98  
% 3.17/0.98  ------ Instantiation Options
% 3.17/0.98  
% 3.17/0.98  --instantiation_flag                    true
% 3.17/0.98  --inst_sos_flag                         false
% 3.17/0.98  --inst_sos_phase                        true
% 3.17/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/0.98  --inst_lit_sel_side                     none
% 3.17/0.98  --inst_solver_per_active                1400
% 3.17/0.98  --inst_solver_calls_frac                1.
% 3.17/0.98  --inst_passive_queue_type               priority_queues
% 3.17/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/0.98  --inst_passive_queues_freq              [25;2]
% 3.17/0.98  --inst_dismatching                      true
% 3.17/0.98  --inst_eager_unprocessed_to_passive     true
% 3.17/0.98  --inst_prop_sim_given                   true
% 3.17/0.98  --inst_prop_sim_new                     false
% 3.17/0.98  --inst_subs_new                         false
% 3.17/0.98  --inst_eq_res_simp                      false
% 3.17/0.98  --inst_subs_given                       false
% 3.17/0.98  --inst_orphan_elimination               true
% 3.17/0.98  --inst_learning_loop_flag               true
% 3.17/0.98  --inst_learning_start                   3000
% 3.17/0.98  --inst_learning_factor                  2
% 3.17/0.98  --inst_start_prop_sim_after_learn       3
% 3.17/0.98  --inst_sel_renew                        solver
% 3.17/0.98  --inst_lit_activity_flag                true
% 3.17/0.98  --inst_restr_to_given                   false
% 3.17/0.98  --inst_activity_threshold               500
% 3.17/0.98  --inst_out_proof                        true
% 3.17/0.98  
% 3.17/0.98  ------ Resolution Options
% 3.17/0.98  
% 3.17/0.98  --resolution_flag                       false
% 3.17/0.98  --res_lit_sel                           adaptive
% 3.17/0.98  --res_lit_sel_side                      none
% 3.17/0.98  --res_ordering                          kbo
% 3.17/0.98  --res_to_prop_solver                    active
% 3.17/0.98  --res_prop_simpl_new                    false
% 3.17/0.98  --res_prop_simpl_given                  true
% 3.17/0.98  --res_passive_queue_type                priority_queues
% 3.17/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/0.98  --res_passive_queues_freq               [15;5]
% 3.17/0.98  --res_forward_subs                      full
% 3.17/0.98  --res_backward_subs                     full
% 3.17/0.98  --res_forward_subs_resolution           true
% 3.17/0.98  --res_backward_subs_resolution          true
% 3.17/0.98  --res_orphan_elimination                true
% 3.17/0.98  --res_time_limit                        2.
% 3.17/0.98  --res_out_proof                         true
% 3.17/0.98  
% 3.17/0.98  ------ Superposition Options
% 3.17/0.98  
% 3.17/0.98  --superposition_flag                    true
% 3.17/0.98  --sup_passive_queue_type                priority_queues
% 3.17/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.17/0.98  --demod_completeness_check              fast
% 3.17/0.98  --demod_use_ground                      true
% 3.17/0.98  --sup_to_prop_solver                    passive
% 3.17/0.98  --sup_prop_simpl_new                    true
% 3.17/0.98  --sup_prop_simpl_given                  true
% 3.17/0.98  --sup_fun_splitting                     false
% 3.17/0.98  --sup_smt_interval                      50000
% 3.17/0.98  
% 3.17/0.98  ------ Superposition Simplification Setup
% 3.17/0.98  
% 3.17/0.98  --sup_indices_passive                   []
% 3.17/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.98  --sup_full_bw                           [BwDemod]
% 3.17/0.98  --sup_immed_triv                        [TrivRules]
% 3.17/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.98  --sup_immed_bw_main                     []
% 3.17/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.98  
% 3.17/0.98  ------ Combination Options
% 3.17/0.98  
% 3.17/0.98  --comb_res_mult                         3
% 3.17/0.98  --comb_sup_mult                         2
% 3.17/0.98  --comb_inst_mult                        10
% 3.17/0.98  
% 3.17/0.98  ------ Debug Options
% 3.17/0.98  
% 3.17/0.98  --dbg_backtrace                         false
% 3.17/0.98  --dbg_dump_prop_clauses                 false
% 3.17/0.98  --dbg_dump_prop_clauses_file            -
% 3.17/0.98  --dbg_out_stat                          false
% 3.17/0.98  
% 3.17/0.98  
% 3.17/0.98  
% 3.17/0.98  
% 3.17/0.98  ------ Proving...
% 3.17/0.98  
% 3.17/0.98  
% 3.17/0.98  % SZS status Theorem for theBenchmark.p
% 3.17/0.98  
% 3.17/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.17/0.98  
% 3.17/0.98  fof(f10,conjecture,(
% 3.17/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.98  
% 3.17/0.98  fof(f11,negated_conjecture,(
% 3.17/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.17/0.98    inference(negated_conjecture,[],[f10])).
% 3.17/0.98  
% 3.17/0.98  fof(f12,plain,(
% 3.17/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.17/0.98    inference(pure_predicate_removal,[],[f11])).
% 3.17/0.98  
% 3.17/0.98  fof(f27,plain,(
% 3.17/0.98    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.17/0.98    inference(ennf_transformation,[],[f12])).
% 3.17/0.98  
% 3.17/0.98  fof(f28,plain,(
% 3.17/0.98    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.17/0.98    inference(flattening,[],[f27])).
% 3.17/0.98  
% 3.17/0.98  fof(f30,plain,(
% 3.17/0.98    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.17/0.98    inference(nnf_transformation,[],[f28])).
% 3.17/0.98  
% 3.17/0.98  fof(f31,plain,(
% 3.17/0.98    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.17/0.98    inference(flattening,[],[f30])).
% 3.17/0.98  
% 3.17/0.98  fof(f33,plain,(
% 3.17/0.98    ( ! [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) => ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(sK1,X0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(sK1,X0))))) )),
% 3.17/0.98    introduced(choice_axiom,[])).
% 3.17/0.98  
% 3.17/0.98  fof(f32,plain,(
% 3.17/0.98    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.17/0.98    introduced(choice_axiom,[])).
% 3.17/0.98  
% 3.17/0.98  fof(f34,plain,(
% 3.17/0.98    ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.17/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 3.17/0.98  
% 3.17/0.98  fof(f56,plain,(
% 3.17/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.17/0.98    inference(cnf_transformation,[],[f34])).
% 3.17/0.98  
% 3.17/0.98  fof(f3,axiom,(
% 3.17/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 3.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.98  
% 3.17/0.98  fof(f16,plain,(
% 3.17/0.98    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.17/0.98    inference(ennf_transformation,[],[f3])).
% 3.17/0.98  
% 3.17/0.98  fof(f17,plain,(
% 3.17/0.98    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.17/0.98    inference(flattening,[],[f16])).
% 3.17/0.98  
% 3.17/0.98  fof(f39,plain,(
% 3.17/0.98    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.17/0.98    inference(cnf_transformation,[],[f17])).
% 3.17/0.98  
% 3.17/0.98  fof(f4,axiom,(
% 3.17/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.98  
% 3.17/0.98  fof(f18,plain,(
% 3.17/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.17/0.98    inference(ennf_transformation,[],[f4])).
% 3.17/0.98  
% 3.17/0.98  fof(f40,plain,(
% 3.17/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.17/0.98    inference(cnf_transformation,[],[f18])).
% 3.17/0.98  
% 3.17/0.98  fof(f52,plain,(
% 3.17/0.98    l1_pre_topc(sK0)),
% 3.17/0.98    inference(cnf_transformation,[],[f34])).
% 3.17/0.98  
% 3.17/0.98  fof(f5,axiom,(
% 3.17/0.98    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.98  
% 3.17/0.98  fof(f19,plain,(
% 3.17/0.98    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.17/0.98    inference(ennf_transformation,[],[f5])).
% 3.17/0.98  
% 3.17/0.98  fof(f41,plain,(
% 3.17/0.98    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.17/0.98    inference(cnf_transformation,[],[f19])).
% 3.17/0.98  
% 3.17/0.98  fof(f2,axiom,(
% 3.17/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.98  
% 3.17/0.98  fof(f15,plain,(
% 3.17/0.98    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.17/0.98    inference(ennf_transformation,[],[f2])).
% 3.17/0.98  
% 3.17/0.98  fof(f37,plain,(
% 3.17/0.98    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.17/0.98    inference(cnf_transformation,[],[f15])).
% 3.17/0.98  
% 3.17/0.98  fof(f1,axiom,(
% 3.17/0.98    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.98  
% 3.17/0.98  fof(f13,plain,(
% 3.17/0.98    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.17/0.98    inference(ennf_transformation,[],[f1])).
% 3.17/0.98  
% 3.17/0.98  fof(f14,plain,(
% 3.17/0.98    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.17/0.98    inference(flattening,[],[f13])).
% 3.17/0.98  
% 3.17/0.98  fof(f35,plain,(
% 3.17/0.98    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.17/0.98    inference(cnf_transformation,[],[f14])).
% 3.17/0.98  
% 3.17/0.98  fof(f36,plain,(
% 3.17/0.98    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.17/0.98    inference(cnf_transformation,[],[f15])).
% 3.17/0.98  
% 3.17/0.98  fof(f9,axiom,(
% 3.17/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 3.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.98  
% 3.17/0.98  fof(f25,plain,(
% 3.17/0.98    ! [X0] : (! [X1] : (((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1) | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.17/0.98    inference(ennf_transformation,[],[f9])).
% 3.17/0.98  
% 3.17/0.98  fof(f26,plain,(
% 3.17/0.98    ! [X0] : (! [X1] : ((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1 | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.17/0.98    inference(flattening,[],[f25])).
% 3.17/0.98  
% 3.17/0.98  fof(f29,plain,(
% 3.17/0.98    ! [X0] : (! [X1] : (((((v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1))) & (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0))) | k1_xboole_0 = X1 | ~v2_pre_topc(X0)) & (((v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1))) & (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.17/0.98    inference(nnf_transformation,[],[f26])).
% 3.17/0.98  
% 3.17/0.98  fof(f49,plain,(
% 3.17/0.98    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0) | k1_xboole_0 = X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.17/0.98    inference(cnf_transformation,[],[f29])).
% 3.17/0.98  
% 3.17/0.98  fof(f7,axiom,(
% 3.17/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.98  
% 3.17/0.98  fof(f22,plain,(
% 3.17/0.98    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.17/0.98    inference(ennf_transformation,[],[f7])).
% 3.17/0.98  
% 3.17/0.98  fof(f44,plain,(
% 3.17/0.98    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.17/0.98    inference(cnf_transformation,[],[f22])).
% 3.17/0.98  
% 3.17/0.98  fof(f51,plain,(
% 3.17/0.98    v2_pre_topc(sK0)),
% 3.17/0.98    inference(cnf_transformation,[],[f34])).
% 3.17/0.98  
% 3.17/0.98  fof(f6,axiom,(
% 3.17/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.98  
% 3.17/0.98  fof(f20,plain,(
% 3.17/0.98    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.17/0.98    inference(ennf_transformation,[],[f6])).
% 3.17/0.98  
% 3.17/0.98  fof(f21,plain,(
% 3.17/0.98    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.17/0.98    inference(flattening,[],[f20])).
% 3.17/0.98  
% 3.17/0.98  fof(f42,plain,(
% 3.17/0.98    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.17/0.98    inference(cnf_transformation,[],[f21])).
% 3.17/0.98  
% 3.17/0.98  fof(f57,plain,(
% 3.17/0.98    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)),
% 3.17/0.98    inference(cnf_transformation,[],[f34])).
% 3.17/0.98  
% 3.17/0.98  fof(f8,axiom,(
% 3.17/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) => (X1 = X2 => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)))))),
% 3.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/0.98  
% 3.17/0.98  fof(f23,plain,(
% 3.17/0.98    ! [X0] : (! [X1] : (! [X2] : ((g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.17/0.98    inference(ennf_transformation,[],[f8])).
% 3.17/0.98  
% 3.17/0.98  fof(f24,plain,(
% 3.17/0.98    ! [X0] : (! [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.17/0.98    inference(flattening,[],[f23])).
% 3.17/0.98  
% 3.17/0.98  fof(f46,plain,(
% 3.17/0.98    ( ! [X2,X0,X1] : (g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.17/0.98    inference(cnf_transformation,[],[f24])).
% 3.17/0.98  
% 3.17/0.98  fof(f58,plain,(
% 3.17/0.98    ( ! [X2,X0] : (g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X2)),u1_pre_topc(k1_pre_topc(X0,X2))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.17/0.98    inference(equality_resolution,[],[f46])).
% 3.17/0.98  
% 3.17/0.98  fof(f38,plain,(
% 3.17/0.98    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.17/0.98    inference(cnf_transformation,[],[f17])).
% 3.17/0.98  
% 3.17/0.98  fof(f55,plain,(
% 3.17/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v2_compts_1(sK1,sK0)),
% 3.17/0.98    inference(cnf_transformation,[],[f34])).
% 3.17/0.98  
% 3.17/0.98  fof(f53,plain,(
% 3.17/0.98    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,sK0)),
% 3.17/0.98    inference(cnf_transformation,[],[f34])).
% 3.17/0.98  
% 3.17/0.98  fof(f43,plain,(
% 3.17/0.98    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.17/0.98    inference(cnf_transformation,[],[f21])).
% 3.17/0.98  
% 3.17/0.98  fof(f50,plain,(
% 3.17/0.98    ( ! [X0,X1] : (v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1)) | k1_xboole_0 = X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.17/0.98    inference(cnf_transformation,[],[f29])).
% 3.17/0.98  
% 3.17/0.98  fof(f48,plain,(
% 3.17/0.98    ( ! [X0,X1] : (v2_compts_1(X1,X0) | ~v1_compts_1(k1_pre_topc(X0,X1)) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.17/0.98    inference(cnf_transformation,[],[f29])).
% 3.17/0.98  
% 3.17/0.98  fof(f59,plain,(
% 3.17/0.98    ( ! [X0] : (v2_compts_1(k1_xboole_0,X0) | ~v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.17/0.98    inference(equality_resolution,[],[f48])).
% 3.17/0.98  
% 3.17/0.98  fof(f47,plain,(
% 3.17/0.98    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.17/0.98    inference(cnf_transformation,[],[f29])).
% 3.17/0.98  
% 3.17/0.98  fof(f60,plain,(
% 3.17/0.98    ( ! [X0] : (v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) | ~v2_compts_1(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.17/0.98    inference(equality_resolution,[],[f47])).
% 3.17/0.98  
% 3.17/0.98  cnf(c_17,negated_conjecture,
% 3.17/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 3.17/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.17/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1148,plain,
% 3.17/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
% 3.17/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_3,plain,
% 3.17/0.98      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 3.17/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.17/0.98      | ~ l1_pre_topc(X0) ),
% 3.17/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_5,plain,
% 3.17/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.17/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_257,plain,
% 3.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.17/0.98      | ~ l1_pre_topc(X1)
% 3.17/0.98      | ~ l1_pre_topc(X2)
% 3.17/0.98      | l1_pre_topc(X3)
% 3.17/0.98      | X2 != X1
% 3.17/0.98      | k1_pre_topc(X1,X0) != X3 ),
% 3.17/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_5]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_258,plain,
% 3.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.17/0.98      | ~ l1_pre_topc(X1)
% 3.17/0.98      | l1_pre_topc(k1_pre_topc(X1,X0)) ),
% 3.17/0.98      inference(unflattening,[status(thm)],[c_257]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1142,plain,
% 3.17/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.17/0.98      | l1_pre_topc(X1) != iProver_top
% 3.17/0.98      | l1_pre_topc(k1_pre_topc(X1,X0)) = iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_258]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1436,plain,
% 3.17/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.17/0.98      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
% 3.17/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_1148,c_1142]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_21,negated_conjecture,
% 3.17/0.98      ( l1_pre_topc(sK0) ),
% 3.17/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_24,plain,
% 3.17/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_6,plain,
% 3.17/0.98      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.17/0.98      | ~ l1_pre_topc(X0) ),
% 3.17/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_55,plain,
% 3.17/0.98      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.17/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_57,plain,
% 3.17/0.98      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 3.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_55]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1,plain,
% 3.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.17/0.98      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.17/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1344,plain,
% 3.17/0.98      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.17/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1345,plain,
% 3.17/0.98      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 3.17/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_1344]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1347,plain,
% 3.17/0.98      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.17/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_1345]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1767,plain,
% 3.17/0.98      ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
% 3.17/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.17/0.98      inference(global_propositional_subsumption,
% 3.17/0.98                [status(thm)],
% 3.17/0.98                [c_1436,c_24,c_57,c_1347]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1768,plain,
% 3.17/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.17/0.98      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top ),
% 3.17/0.98      inference(renaming,[status(thm)],[c_1767]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1159,plain,
% 3.17/0.98      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.17/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1162,plain,
% 3.17/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.17/0.98      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1620,plain,
% 3.17/0.98      ( l1_pre_topc(X0) != iProver_top
% 3.17/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_1159,c_1162]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_0,plain,
% 3.17/0.98      ( ~ l1_pre_topc(X0)
% 3.17/0.98      | ~ v1_pre_topc(X0)
% 3.17/0.98      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.17/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1163,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 3.17/0.98      | l1_pre_topc(X0) != iProver_top
% 3.17/0.98      | v1_pre_topc(X0) != iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1914,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 3.17/0.98      | l1_pre_topc(X0) != iProver_top
% 3.17/0.98      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_1620,c_1163]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1358,plain,
% 3.17/0.98      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.17/0.98      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.17/0.98      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1359,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 3.17/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 3.17/0.98      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_1358]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_2,plain,
% 3.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.17/0.98      | v1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.17/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1161,plain,
% 3.17/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.17/0.98      | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1528,plain,
% 3.17/0.98      ( l1_pre_topc(X0) != iProver_top
% 3.17/0.98      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_1159,c_1161]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_2542,plain,
% 3.17/0.98      ( l1_pre_topc(X0) != iProver_top
% 3.17/0.98      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.17/0.98      inference(global_propositional_subsumption,
% 3.17/0.98                [status(thm)],
% 3.17/0.98                [c_1914,c_1359,c_1528,c_1620]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_2543,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 3.17/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.17/0.98      inference(renaming,[status(thm)],[c_2542]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_2552,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))),u1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))))) = g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))
% 3.17/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_1768,c_2543]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_13,plain,
% 3.17/0.98      ( ~ v2_compts_1(X0,X1)
% 3.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.17/0.98      | v1_compts_1(k1_pre_topc(X1,X0))
% 3.17/0.98      | ~ v2_pre_topc(X1)
% 3.17/0.98      | ~ l1_pre_topc(X1)
% 3.17/0.98      | k1_xboole_0 = X0 ),
% 3.17/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1152,plain,
% 3.17/0.98      ( k1_xboole_0 = X0
% 3.17/0.98      | v2_compts_1(X0,X1) != iProver_top
% 3.17/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.17/0.98      | v1_compts_1(k1_pre_topc(X1,X0)) = iProver_top
% 3.17/0.98      | v2_pre_topc(X1) != iProver_top
% 3.17/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_3614,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))),u1_pre_topc(g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))))) = g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))
% 3.17/0.98      | sK1 = k1_xboole_0
% 3.17/0.98      | v2_compts_1(sK1,sK0) != iProver_top
% 3.17/0.98      | v1_compts_1(k1_pre_topc(sK0,sK1)) = iProver_top
% 3.17/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_2552,c_1152]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1144,plain,
% 3.17/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_2550,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_1144,c_2543]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_10,plain,
% 3.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.17/0.98      | X2 = X1
% 3.17/0.98      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 3.17/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1155,plain,
% 3.17/0.98      ( X0 = X1
% 3.17/0.98      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 3.17/0.98      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_2667,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
% 3.17/0.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
% 3.17/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_2550,c_1155]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_2888,plain,
% 3.17/0.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0)
% 3.17/0.98      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 3.17/0.98      inference(equality_resolution,[status(thm)],[c_2667]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_22,negated_conjecture,
% 3.17/0.98      ( v2_pre_topc(sK0) ),
% 3.17/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_56,plain,
% 3.17/0.98      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.17/0.98      | ~ l1_pre_topc(sK0) ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_8,plain,
% 3.17/0.98      ( ~ v2_pre_topc(X0)
% 3.17/0.98      | ~ l1_pre_topc(X0)
% 3.17/0.98      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.17/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_315,plain,
% 3.17/0.98      ( ~ v2_pre_topc(X0)
% 3.17/0.98      | ~ l1_pre_topc(X1)
% 3.17/0.98      | ~ l1_pre_topc(X0)
% 3.17/0.98      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != X1
% 3.17/0.98      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X1 ),
% 3.17/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_8]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_316,plain,
% 3.17/0.98      ( ~ v2_pre_topc(X0)
% 3.17/0.98      | ~ l1_pre_topc(X0)
% 3.17/0.98      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.17/0.98      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.17/0.98      inference(unflattening,[status(thm)],[c_315]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_318,plain,
% 3.17/0.98      ( ~ v2_pre_topc(sK0)
% 3.17/0.98      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.17/0.98      | ~ l1_pre_topc(sK0)
% 3.17/0.98      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_316]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1346,plain,
% 3.17/0.98      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.17/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_1344]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1803,plain,
% 3.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.17/0.98      | X1 = u1_struct_0(sK0)
% 3.17/0.98      | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK0),X0) ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_2159,plain,
% 3.17/0.98      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.17/0.98      | X0 = u1_struct_0(sK0)
% 3.17/0.98      | g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_1803]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_2656,plain,
% 3.17/0.98      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.17/0.98      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
% 3.17/0.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0) ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_2159]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_3743,plain,
% 3.17/0.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0) ),
% 3.17/0.98      inference(global_propositional_subsumption,
% 3.17/0.98                [status(thm)],
% 3.17/0.98                [c_2888,c_22,c_21,c_56,c_318,c_1346,c_2656]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_3751,plain,
% 3.17/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.17/0.98      inference(demodulation,[status(thm)],[c_3743,c_1148]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_16,negated_conjecture,
% 3.17/0.98      ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.17/0.98      | ~ v2_compts_1(sK1,sK0)
% 3.17/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 3.17/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.17/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1149,plain,
% 3.17/0.98      ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.17/0.98      | v2_compts_1(sK1,sK0) != iProver_top
% 3.17/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
% 3.17/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_3753,plain,
% 3.17/0.98      ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.17/0.98      | v2_compts_1(sK1,sK0) != iProver_top
% 3.17/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.17/0.98      inference(demodulation,[status(thm)],[c_3743,c_1149]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_3766,plain,
% 3.17/0.98      ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.17/0.98      | v2_compts_1(sK1,sK0) != iProver_top ),
% 3.17/0.98      inference(backward_subsumption_resolution,
% 3.17/0.98                [status(thm)],
% 3.17/0.98                [c_3751,c_3753]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_11,plain,
% 3.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 3.17/0.98      | ~ l1_pre_topc(X1)
% 3.17/0.98      | g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ),
% 3.17/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1154,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.17/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.17/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) != iProver_top
% 3.17/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_3814,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,X0)),u1_pre_topc(k1_pre_topc(sK0,X0))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
% 3.17/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_3743,c_1154]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_5618,plain,
% 3.17/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.17/0.98      | g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,X0)),u1_pre_topc(k1_pre_topc(sK0,X0))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) ),
% 3.17/0.98      inference(global_propositional_subsumption,
% 3.17/0.98                [status(thm)],
% 3.17/0.98                [c_3814,c_24]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_5619,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,X0)),u1_pre_topc(k1_pre_topc(sK0,X0))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
% 3.17/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.17/0.98      inference(renaming,[status(thm)],[c_5618]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_5626,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_3751,c_5619]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_3929,plain,
% 3.17/0.98      ( l1_pre_topc(k1_pre_topc(sK0,sK1)) = iProver_top
% 3.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_3751,c_1142]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1374,plain,
% 3.17/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.17/0.98      | l1_pre_topc(k1_pre_topc(sK0,sK1))
% 3.17/0.98      | ~ l1_pre_topc(sK0) ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_258]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1375,plain,
% 3.17/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.17/0.98      | l1_pre_topc(k1_pre_topc(sK0,sK1)) = iProver_top
% 3.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_1374]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_4065,plain,
% 3.17/0.98      ( l1_pre_topc(k1_pre_topc(sK0,sK1)) = iProver_top ),
% 3.17/0.98      inference(global_propositional_subsumption,
% 3.17/0.98                [status(thm)],
% 3.17/0.98                [c_3929,c_24,c_1375,c_3751]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_4071,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(sK0,sK1)
% 3.17/0.98      | v1_pre_topc(k1_pre_topc(sK0,sK1)) != iProver_top ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_4065,c_1163]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_4,plain,
% 3.17/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.17/0.98      | ~ l1_pre_topc(X1)
% 3.17/0.98      | v1_pre_topc(k1_pre_topc(X1,X0)) ),
% 3.17/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1371,plain,
% 3.17/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.17/0.98      | ~ l1_pre_topc(sK0)
% 3.17/0.98      | v1_pre_topc(k1_pre_topc(sK0,sK1)) ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1372,plain,
% 3.17/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.17/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.17/0.98      | v1_pre_topc(k1_pre_topc(sK0,sK1)) = iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_1371]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1412,plain,
% 3.17/0.98      ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
% 3.17/0.98      | ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
% 3.17/0.98      | g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(sK0,sK1) ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1413,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(sK0,sK1)
% 3.17/0.98      | l1_pre_topc(k1_pre_topc(sK0,sK1)) != iProver_top
% 3.17/0.98      | v1_pre_topc(k1_pre_topc(sK0,sK1)) != iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_1412]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_4283,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(sK0,sK1) ),
% 3.17/0.98      inference(global_propositional_subsumption,
% 3.17/0.98                [status(thm)],
% 3.17/0.98                [c_4071,c_24,c_1372,c_1375,c_1413,c_3751]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_5627,plain,
% 3.17/0.98      ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1) ),
% 3.17/0.98      inference(light_normalisation,[status(thm)],[c_5626,c_4283]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_18,negated_conjecture,
% 3.17/0.98      ( v2_compts_1(sK1,sK0)
% 3.17/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
% 3.17/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1147,plain,
% 3.17/0.98      ( v2_compts_1(sK1,sK0) = iProver_top
% 3.17/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_2422,plain,
% 3.17/0.98      ( sK1 = k1_xboole_0
% 3.17/0.98      | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.17/0.98      | v2_compts_1(sK1,sK0) = iProver_top
% 3.17/0.98      | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
% 3.17/0.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.17/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_1147,c_1152]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_23,plain,
% 3.17/0.98      ( v2_pre_topc(sK0) = iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_20,negated_conjecture,
% 3.17/0.98      ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.17/0.98      | v2_compts_1(sK1,sK0) ),
% 3.17/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_25,plain,
% 3.17/0.98      ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.17/0.98      | v2_compts_1(sK1,sK0) = iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_7,plain,
% 3.17/0.98      ( ~ v2_pre_topc(X0)
% 3.17/0.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.17/0.98      | ~ l1_pre_topc(X0) ),
% 3.17/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_52,plain,
% 3.17/0.98      ( v2_pre_topc(X0) != iProver_top
% 3.17/0.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 3.17/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_54,plain,
% 3.17/0.98      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.17/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_52]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_2809,plain,
% 3.17/0.98      ( sK1 = k1_xboole_0
% 3.17/0.98      | v2_compts_1(sK1,sK0) = iProver_top
% 3.17/0.98      | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top ),
% 3.17/0.98      inference(global_propositional_subsumption,
% 3.17/0.98                [status(thm)],
% 3.17/0.98                [c_2422,c_23,c_24,c_25,c_54,c_57,c_1347]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_5891,plain,
% 3.17/0.98      ( sK1 = k1_xboole_0
% 3.17/0.98      | v2_compts_1(sK1,sK0) = iProver_top
% 3.17/0.98      | v1_compts_1(k1_pre_topc(sK0,sK1)) = iProver_top ),
% 3.17/0.98      inference(demodulation,[status(thm)],[c_5627,c_2809]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1160,plain,
% 3.17/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.17/0.98      | l1_pre_topc(X1) != iProver_top
% 3.17/0.98      | v1_pre_topc(k1_pre_topc(X1,X0)) = iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_2046,plain,
% 3.17/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.17/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.17/0.98      | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_1148,c_1160]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_2151,plain,
% 3.17/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.17/0.98      | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top ),
% 3.17/0.98      inference(global_propositional_subsumption,
% 3.17/0.98                [status(thm)],
% 3.17/0.98                [c_2046,c_24,c_57,c_1347]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1773,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.17/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.17/0.98      | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_1768,c_1163]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_2157,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.17/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_2151,c_1773]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_2423,plain,
% 3.17/0.98      ( g1_pre_topc(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.17/0.98      | sK1 = k1_xboole_0
% 3.17/0.98      | v2_compts_1(sK1,sK0) != iProver_top
% 3.17/0.98      | v1_compts_1(k1_pre_topc(sK0,sK1)) = iProver_top
% 3.17/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_2157,c_1152]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_3927,plain,
% 3.17/0.98      ( sK1 = k1_xboole_0
% 3.17/0.98      | v2_compts_1(sK1,sK0) != iProver_top
% 3.17/0.98      | v1_compts_1(k1_pre_topc(sK0,sK1)) = iProver_top
% 3.17/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_3751,c_1152]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_4212,plain,
% 3.17/0.98      ( sK1 = k1_xboole_0
% 3.17/0.98      | v2_compts_1(sK1,sK0) != iProver_top
% 3.17/0.98      | v1_compts_1(k1_pre_topc(sK0,sK1)) = iProver_top ),
% 3.17/0.98      inference(global_propositional_subsumption,
% 3.17/0.98                [status(thm)],
% 3.17/0.98                [c_2423,c_23,c_24,c_3927]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_6063,plain,
% 3.17/0.98      ( sK1 = k1_xboole_0
% 3.17/0.98      | v1_compts_1(k1_pre_topc(sK0,sK1)) = iProver_top ),
% 3.17/0.98      inference(global_propositional_subsumption,
% 3.17/0.98                [status(thm)],
% 3.17/0.98                [c_5891,c_4212]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_12,plain,
% 3.17/0.98      ( v2_compts_1(X0,X1)
% 3.17/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.17/0.98      | ~ v1_compts_1(k1_pre_topc(X1,X0))
% 3.17/0.98      | ~ v2_pre_topc(X1)
% 3.17/0.98      | ~ l1_pre_topc(X1)
% 3.17/0.98      | k1_xboole_0 = X0 ),
% 3.17/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1153,plain,
% 3.17/0.98      ( k1_xboole_0 = X0
% 3.17/0.98      | v2_compts_1(X0,X1) = iProver_top
% 3.17/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.17/0.98      | v1_compts_1(k1_pre_topc(X1,X0)) != iProver_top
% 3.17/0.98      | v2_pre_topc(X1) != iProver_top
% 3.17/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_3926,plain,
% 3.17/0.98      ( sK1 = k1_xboole_0
% 3.17/0.98      | v2_compts_1(sK1,sK0) = iProver_top
% 3.17/0.98      | v1_compts_1(k1_pre_topc(sK0,sK1)) != iProver_top
% 3.17/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.17/0.98      inference(superposition,[status(thm)],[c_3751,c_1153]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1419,plain,
% 3.17/0.98      ( v2_compts_1(sK1,sK0)
% 3.17/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.17/0.98      | ~ v1_compts_1(k1_pre_topc(sK0,sK1))
% 3.17/0.98      | ~ v2_pre_topc(sK0)
% 3.17/0.98      | ~ l1_pre_topc(sK0)
% 3.17/0.98      | k1_xboole_0 = sK1 ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1420,plain,
% 3.17/0.98      ( k1_xboole_0 = sK1
% 3.17/0.98      | v2_compts_1(sK1,sK0) = iProver_top
% 3.17/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.17/0.98      | v1_compts_1(k1_pre_topc(sK0,sK1)) != iProver_top
% 3.17/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.17/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.17/0.98      inference(predicate_to_equality,[status(thm)],[c_1419]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_716,plain,( X0 = X0 ),theory(equality) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1463,plain,
% 3.17/0.98      ( sK1 = sK1 ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_716]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_717,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1586,plain,
% 3.17/0.98      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_717]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_1842,plain,
% 3.17/0.98      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 3.17/0.98      inference(instantiation,[status(thm)],[c_1586]) ).
% 3.17/0.98  
% 3.17/0.98  cnf(c_4646,plain,
% 3.17/0.99      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_1842]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_4711,plain,
% 3.17/0.99      ( sK1 = k1_xboole_0
% 3.17/0.99      | v2_compts_1(sK1,sK0) = iProver_top
% 3.17/0.99      | v1_compts_1(k1_pre_topc(sK0,sK1)) != iProver_top ),
% 3.17/0.99      inference(global_propositional_subsumption,
% 3.17/0.99                [status(thm)],
% 3.17/0.99                [c_3926,c_23,c_24,c_1420,c_1463,c_3751,c_4646]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6069,plain,
% 3.17/0.99      ( sK1 = k1_xboole_0 | v2_compts_1(sK1,sK0) = iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_6063,c_4711]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3810,plain,
% 3.17/0.99      ( k1_xboole_0 = X0
% 3.17/0.99      | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.17/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.17/0.99      | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) != iProver_top
% 3.17/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.17/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_3743,c_1153]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6298,plain,
% 3.17/0.99      ( k1_xboole_0 = X0
% 3.17/0.99      | v2_compts_1(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.17/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.17/0.99      | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)) != iProver_top ),
% 3.17/0.99      inference(global_propositional_subsumption,
% 3.17/0.99                [status(thm)],
% 3.17/0.99                [c_3810,c_23,c_24,c_54,c_57,c_1347]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6309,plain,
% 3.17/0.99      ( sK1 = k1_xboole_0
% 3.17/0.99      | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.17/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.17/0.99      | v1_compts_1(k1_pre_topc(sK0,sK1)) != iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_5627,c_6298]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6503,plain,
% 3.17/0.99      ( sK1 = k1_xboole_0 ),
% 3.17/0.99      inference(global_propositional_subsumption,
% 3.17/0.99                [status(thm)],
% 3.17/0.99                [c_3614,c_3751,c_3766,c_6063,c_6069,c_6309]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6506,plain,
% 3.17/0.99      ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0) = k1_pre_topc(sK0,k1_xboole_0) ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_6503,c_5627]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_14,plain,
% 3.17/0.99      ( v2_compts_1(k1_xboole_0,X0)
% 3.17/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 3.17/0.99      | ~ v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
% 3.17/0.99      | ~ l1_pre_topc(X0) ),
% 3.17/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_1151,plain,
% 3.17/0.99      ( v2_compts_1(k1_xboole_0,X0) = iProver_top
% 3.17/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.17/0.99      | v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) != iProver_top
% 3.17/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3804,plain,
% 3.17/0.99      ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.17/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.17/0.99      | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) != iProver_top
% 3.17/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_3743,c_1151]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_5879,plain,
% 3.17/0.99      ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) != iProver_top
% 3.17/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.17/0.99      | v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 3.17/0.99      inference(global_propositional_subsumption,
% 3.17/0.99                [status(thm)],
% 3.17/0.99                [c_3804,c_24,c_57,c_1347]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_5880,plain,
% 3.17/0.99      ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.17/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.17/0.99      | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) != iProver_top ),
% 3.17/0.99      inference(renaming,[status(thm)],[c_5879]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_7566,plain,
% 3.17/0.99      ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.17/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.17/0.99      | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) != iProver_top ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_6506,c_5880]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_15,plain,
% 3.17/0.99      ( ~ v2_compts_1(k1_xboole_0,X0)
% 3.17/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 3.17/0.99      | v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
% 3.17/0.99      | ~ l1_pre_topc(X0) ),
% 3.17/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_1150,plain,
% 3.17/0.99      ( v2_compts_1(k1_xboole_0,X0) != iProver_top
% 3.17/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.17/0.99      | v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) = iProver_top
% 3.17/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3806,plain,
% 3.17/0.99      ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.17/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.17/0.99      | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) = iProver_top
% 3.17/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_3743,c_1150]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6284,plain,
% 3.17/0.99      ( v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) = iProver_top
% 3.17/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.17/0.99      | v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 3.17/0.99      inference(global_propositional_subsumption,
% 3.17/0.99                [status(thm)],
% 3.17/0.99                [c_3806,c_24,c_57,c_1347]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6285,plain,
% 3.17/0.99      ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.17/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.17/0.99      | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_xboole_0)) = iProver_top ),
% 3.17/0.99      inference(renaming,[status(thm)],[c_6284]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_7565,plain,
% 3.17/0.99      ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.17/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.17/0.99      | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) = iProver_top ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_6506,c_6285]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6515,plain,
% 3.17/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_6503,c_3751]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6805,plain,
% 3.17/0.99      ( v2_compts_1(k1_xboole_0,sK0) != iProver_top
% 3.17/0.99      | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) = iProver_top
% 3.17/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_6515,c_1150]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6940,plain,
% 3.17/0.99      ( v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) = iProver_top
% 3.17/0.99      | v2_compts_1(k1_xboole_0,sK0) != iProver_top ),
% 3.17/0.99      inference(global_propositional_subsumption,
% 3.17/0.99                [status(thm)],
% 3.17/0.99                [c_6805,c_24]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6941,plain,
% 3.17/0.99      ( v2_compts_1(k1_xboole_0,sK0) != iProver_top
% 3.17/0.99      | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) = iProver_top ),
% 3.17/0.99      inference(renaming,[status(thm)],[c_6940]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6804,plain,
% 3.17/0.99      ( v2_compts_1(k1_xboole_0,sK0) = iProver_top
% 3.17/0.99      | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) != iProver_top
% 3.17/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_6515,c_1151]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6827,plain,
% 3.17/0.99      ( v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) != iProver_top
% 3.17/0.99      | v2_compts_1(k1_xboole_0,sK0) = iProver_top ),
% 3.17/0.99      inference(global_propositional_subsumption,
% 3.17/0.99                [status(thm)],
% 3.17/0.99                [c_6804,c_24]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6828,plain,
% 3.17/0.99      ( v2_compts_1(k1_xboole_0,sK0) = iProver_top
% 3.17/0.99      | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) != iProver_top ),
% 3.17/0.99      inference(renaming,[status(thm)],[c_6827]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_1145,plain,
% 3.17/0.99      ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.17/0.99      | v2_compts_1(sK1,sK0) = iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6517,plain,
% 3.17/0.99      ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.17/0.99      | v2_compts_1(k1_xboole_0,sK0) = iProver_top ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_6503,c_1145]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6509,plain,
% 3.17/0.99      ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.17/0.99      | v2_compts_1(k1_xboole_0,sK0) != iProver_top ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_6503,c_3766]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(contradiction,plain,
% 3.17/0.99      ( $false ),
% 3.17/0.99      inference(minisat,
% 3.17/0.99                [status(thm)],
% 3.17/0.99                [c_7566,c_7565,c_6941,c_6828,c_6517,c_6515,c_6509]) ).
% 3.17/0.99  
% 3.17/0.99  
% 3.17/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.17/0.99  
% 3.17/0.99  ------                               Statistics
% 3.17/0.99  
% 3.17/0.99  ------ General
% 3.17/0.99  
% 3.17/0.99  abstr_ref_over_cycles:                  0
% 3.17/0.99  abstr_ref_under_cycles:                 0
% 3.17/0.99  gc_basic_clause_elim:                   0
% 3.17/0.99  forced_gc_time:                         0
% 3.17/0.99  parsing_time:                           0.01
% 3.17/0.99  unif_index_cands_time:                  0.
% 3.17/0.99  unif_index_add_time:                    0.
% 3.17/0.99  orderings_time:                         0.
% 3.17/0.99  out_proof_time:                         0.012
% 3.17/0.99  total_time:                             0.251
% 3.17/0.99  num_of_symbols:                         46
% 3.17/0.99  num_of_terms:                           5649
% 3.17/0.99  
% 3.17/0.99  ------ Preprocessing
% 3.17/0.99  
% 3.17/0.99  num_of_splits:                          0
% 3.17/0.99  num_of_split_atoms:                     0
% 3.17/0.99  num_of_reused_defs:                     0
% 3.17/0.99  num_eq_ax_congr_red:                    1
% 3.17/0.99  num_of_sem_filtered_clauses:            1
% 3.17/0.99  num_of_subtypes:                        0
% 3.17/0.99  monotx_restored_types:                  0
% 3.17/0.99  sat_num_of_epr_types:                   0
% 3.17/0.99  sat_num_of_non_cyclic_types:            0
% 3.17/0.99  sat_guarded_non_collapsed_types:        0
% 3.17/0.99  num_pure_diseq_elim:                    0
% 3.17/0.99  simp_replaced_by:                       0
% 3.17/0.99  res_preprocessed:                       116
% 3.17/0.99  prep_upred:                             0
% 3.17/0.99  prep_unflattend:                        8
% 3.17/0.99  smt_new_axioms:                         0
% 3.17/0.99  pred_elim_cands:                        6
% 3.17/0.99  pred_elim:                              1
% 3.17/0.99  pred_elim_cl:                           1
% 3.17/0.99  pred_elim_cycles:                       5
% 3.17/0.99  merged_defs:                            0
% 3.17/0.99  merged_defs_ncl:                        0
% 3.17/0.99  bin_hyper_res:                          0
% 3.17/0.99  prep_cycles:                            4
% 3.17/0.99  pred_elim_time:                         0.006
% 3.17/0.99  splitting_time:                         0.
% 3.17/0.99  sem_filter_time:                        0.
% 3.17/0.99  monotx_time:                            0.
% 3.17/0.99  subtype_inf_time:                       0.
% 3.17/0.99  
% 3.17/0.99  ------ Problem properties
% 3.17/0.99  
% 3.17/0.99  clauses:                                22
% 3.17/0.99  conjectures:                            7
% 3.17/0.99  epr:                                    2
% 3.17/0.99  horn:                                   16
% 3.17/0.99  ground:                                 7
% 3.17/0.99  unary:                                  2
% 3.17/0.99  binary:                                 7
% 3.17/0.99  lits:                                   65
% 3.17/0.99  lits_eq:                                8
% 3.17/0.99  fd_pure:                                0
% 3.17/0.99  fd_pseudo:                              0
% 3.17/0.99  fd_cond:                                2
% 3.17/0.99  fd_pseudo_cond:                         2
% 3.17/0.99  ac_symbols:                             0
% 3.17/0.99  
% 3.17/0.99  ------ Propositional Solver
% 3.17/0.99  
% 3.17/0.99  prop_solver_calls:                      31
% 3.17/0.99  prop_fast_solver_calls:                 1304
% 3.17/0.99  smt_solver_calls:                       0
% 3.17/0.99  smt_fast_solver_calls:                  0
% 3.17/0.99  prop_num_of_clauses:                    1899
% 3.17/0.99  prop_preprocess_simplified:             6246
% 3.17/0.99  prop_fo_subsumed:                       105
% 3.17/0.99  prop_solver_time:                       0.
% 3.17/0.99  smt_solver_time:                        0.
% 3.17/0.99  smt_fast_solver_time:                   0.
% 3.17/0.99  prop_fast_solver_time:                  0.
% 3.17/0.99  prop_unsat_core_time:                   0.
% 3.17/0.99  
% 3.17/0.99  ------ QBF
% 3.17/0.99  
% 3.17/0.99  qbf_q_res:                              0
% 3.17/0.99  qbf_num_tautologies:                    0
% 3.17/0.99  qbf_prep_cycles:                        0
% 3.17/0.99  
% 3.17/0.99  ------ BMC1
% 3.17/0.99  
% 3.17/0.99  bmc1_current_bound:                     -1
% 3.17/0.99  bmc1_last_solved_bound:                 -1
% 3.17/0.99  bmc1_unsat_core_size:                   -1
% 3.17/0.99  bmc1_unsat_core_parents_size:           -1
% 3.17/0.99  bmc1_merge_next_fun:                    0
% 3.17/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.17/0.99  
% 3.17/0.99  ------ Instantiation
% 3.17/0.99  
% 3.17/0.99  inst_num_of_clauses:                    687
% 3.17/0.99  inst_num_in_passive:                    125
% 3.17/0.99  inst_num_in_active:                     477
% 3.17/0.99  inst_num_in_unprocessed:                85
% 3.17/0.99  inst_num_of_loops:                      550
% 3.17/0.99  inst_num_of_learning_restarts:          0
% 3.17/0.99  inst_num_moves_active_passive:          66
% 3.17/0.99  inst_lit_activity:                      0
% 3.17/0.99  inst_lit_activity_moves:                0
% 3.17/0.99  inst_num_tautologies:                   0
% 3.17/0.99  inst_num_prop_implied:                  0
% 3.17/0.99  inst_num_existing_simplified:           0
% 3.17/0.99  inst_num_eq_res_simplified:             0
% 3.17/0.99  inst_num_child_elim:                    0
% 3.17/0.99  inst_num_of_dismatching_blockings:      1336
% 3.17/0.99  inst_num_of_non_proper_insts:           1919
% 3.17/0.99  inst_num_of_duplicates:                 0
% 3.17/0.99  inst_inst_num_from_inst_to_res:         0
% 3.17/0.99  inst_dismatching_checking_time:         0.
% 3.17/0.99  
% 3.17/0.99  ------ Resolution
% 3.17/0.99  
% 3.17/0.99  res_num_of_clauses:                     0
% 3.17/0.99  res_num_in_passive:                     0
% 3.17/0.99  res_num_in_active:                      0
% 3.17/0.99  res_num_of_loops:                       120
% 3.17/0.99  res_forward_subset_subsumed:            149
% 3.17/0.99  res_backward_subset_subsumed:           2
% 3.17/0.99  res_forward_subsumed:                   0
% 3.17/0.99  res_backward_subsumed:                  0
% 3.17/0.99  res_forward_subsumption_resolution:     0
% 3.17/0.99  res_backward_subsumption_resolution:    0
% 3.17/0.99  res_clause_to_clause_subsumption:       285
% 3.17/0.99  res_orphan_elimination:                 0
% 3.17/0.99  res_tautology_del:                      277
% 3.17/0.99  res_num_eq_res_simplified:              0
% 3.17/0.99  res_num_sel_changes:                    0
% 3.17/0.99  res_moves_from_active_to_pass:          0
% 3.17/0.99  
% 3.17/0.99  ------ Superposition
% 3.17/0.99  
% 3.17/0.99  sup_time_total:                         0.
% 3.17/0.99  sup_time_generating:                    0.
% 3.17/0.99  sup_time_sim_full:                      0.
% 3.17/0.99  sup_time_sim_immed:                     0.
% 3.17/0.99  
% 3.17/0.99  sup_num_of_clauses:                     87
% 3.17/0.99  sup_num_in_active:                      54
% 3.17/0.99  sup_num_in_passive:                     33
% 3.17/0.99  sup_num_of_loops:                       108
% 3.17/0.99  sup_fw_superposition:                   79
% 3.17/0.99  sup_bw_superposition:                   149
% 3.17/0.99  sup_immediate_simplified:               58
% 3.17/0.99  sup_given_eliminated:                   0
% 3.17/0.99  comparisons_done:                       0
% 3.17/0.99  comparisons_avoided:                    3
% 3.17/0.99  
% 3.17/0.99  ------ Simplifications
% 3.17/0.99  
% 3.17/0.99  
% 3.17/0.99  sim_fw_subset_subsumed:                 25
% 3.17/0.99  sim_bw_subset_subsumed:                 26
% 3.17/0.99  sim_fw_subsumed:                        5
% 3.17/0.99  sim_bw_subsumed:                        2
% 3.17/0.99  sim_fw_subsumption_res:                 0
% 3.17/0.99  sim_bw_subsumption_res:                 1
% 3.17/0.99  sim_tautology_del:                      24
% 3.17/0.99  sim_eq_tautology_del:                   42
% 3.17/0.99  sim_eq_res_simp:                        0
% 3.17/0.99  sim_fw_demodulated:                     1
% 3.17/0.99  sim_bw_demodulated:                     39
% 3.17/0.99  sim_light_normalised:                   61
% 3.17/0.99  sim_joinable_taut:                      0
% 3.17/0.99  sim_joinable_simp:                      0
% 3.17/0.99  sim_ac_normalised:                      0
% 3.17/0.99  sim_smt_subsumption:                    0
% 3.17/0.99  
%------------------------------------------------------------------------------
