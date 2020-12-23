%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:09 EST 2020

% Result     : Theorem 15.34s
% Output     : CNFRefutation 15.34s
% Verified   : 
% Statistics : Number of formulae       :  214 (2510 expanded)
%              Number of clauses        :  151 ( 978 expanded)
%              Number of leaves         :   20 ( 459 expanded)
%              Depth                    :   26
%              Number of atoms          :  721 (11482 expanded)
%              Number of equality atoms :  303 (1605 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_compts_1(X2,X0)
                    <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <=> v2_compts_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <=> v2_compts_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v2_compts_1(X2,X0)
                      | ~ v2_compts_1(X3,X1) )
                    & ( v2_compts_1(X3,X1)
                      | ~ v2_compts_1(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(X3,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X0)
      | ~ v2_compts_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f18,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
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
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f39,plain,(
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
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f41,plain,(
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

fof(f40,plain,
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
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v2_compts_1(X1,sK0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
              & v2_compts_1(X1,sK0) ) ) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_compts_1(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v2_compts_1(sK1,sK0) ) )
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).

fof(f63,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X3,X1)
      | ~ v2_compts_1(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X1)
      | ~ v2_compts_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1137,plain,
    ( ~ v2_compts_1(sK1,X0)
    | v2_compts_1(sK1,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3550,plain,
    ( ~ v2_compts_1(sK1,X0)
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_1137])).

cnf(c_67742,plain,
    ( ~ v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_3550])).

cnf(c_23,negated_conjecture,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_781,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_compts_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_137,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_9])).

cnf(c_138,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_137])).

cnf(c_779,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_138])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_780,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_0,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_803,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_790,plain,
    ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1932,plain,
    ( u1_struct_0(k1_pre_topc(X0,k1_xboole_0)) = k1_xboole_0
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_790])).

cnf(c_3349,plain,
    ( u1_struct_0(k1_pre_topc(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_780,c_1932])).

cnf(c_18,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_786,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_789,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_928,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_786,c_789])).

cnf(c_3442,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,k1_pre_topc(sK0,k1_xboole_0)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3349,c_928])).

cnf(c_4505,plain,
    ( v2_compts_1(X0,k1_pre_topc(sK0,k1_xboole_0)) = iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_779,c_3442])).

cnf(c_10,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_793,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_798,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1346,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_798])).

cnf(c_58575,plain,
    ( v2_compts_1(X0,k1_pre_topc(sK0,k1_xboole_0)) = iProver_top
    | v2_compts_1(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4505,c_1346])).

cnf(c_58580,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,k1_xboole_0)) = iProver_top
    | v2_compts_1(sK1,sK0) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_781,c_58575])).

cnf(c_25,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_26,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_compts_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_47,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_49,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_1011,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1012,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1011])).

cnf(c_1014,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_7,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1052,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1053,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1052])).

cnf(c_1119,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_138])).

cnf(c_1120,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1119])).

cnf(c_322,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1167,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_323,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_1429,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_2157,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1429])).

cnf(c_3084,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) != sK1
    | sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2157])).

cnf(c_1,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3147,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))))
    | k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0) = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3165,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_1002,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2289,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_4903,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))) ),
    inference(instantiation,[status(thm)],[c_2289])).

cnf(c_4904,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4903])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1198,plain,
    ( m1_subset_1(k8_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(X0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1499,plain,
    ( m1_subset_1(k8_setfam_1(u1_struct_0(X0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ),
    inference(instantiation,[status(thm)],[c_1198])).

cnf(c_5174,plain,
    ( m1_subset_1(k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))) ),
    inference(instantiation,[status(thm)],[c_1499])).

cnf(c_5177,plain,
    ( m1_subset_1(k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5174])).

cnf(c_3332,plain,
    ( X0 != u1_struct_0(k1_pre_topc(sK0,sK1))
    | sK1 = X0
    | sK1 != u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1429])).

cnf(c_9951,plain,
    ( k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0) != u1_struct_0(k1_pre_topc(sK0,sK1))
    | sK1 = k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0)
    | sK1 != u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_3332])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_784,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1934,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_784,c_790])).

cnf(c_2166,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1934,c_25,c_49,c_1014])).

cnf(c_2167,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2166])).

cnf(c_2172,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2167,c_790])).

cnf(c_2175,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
    | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2172,c_25])).

cnf(c_2176,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
    inference(renaming,[status(thm)],[c_2175])).

cnf(c_15,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_788,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2183,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
    | m1_pre_topc(X0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2176,c_788])).

cnf(c_48,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1013,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_1063,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_796,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2787,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_784,c_796])).

cnf(c_3115,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2787,c_25,c_49,c_1014])).

cnf(c_3116,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3115])).

cnf(c_794,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3121,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3116,c_794])).

cnf(c_3137,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3121])).

cnf(c_3122,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3116,c_788])).

cnf(c_3138,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3122])).

cnf(c_802,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_810,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_802,c_803])).

cnf(c_800,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1667,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_810,c_800])).

cnf(c_1007,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1002])).

cnf(c_1739,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1667,c_1007])).

cnf(c_2588,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_789])).

cnf(c_7623,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2176,c_2588])).

cnf(c_7753,plain,
    ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7623])).

cnf(c_7755,plain,
    ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_7753])).

cnf(c_12657,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2183,c_24,c_48,c_1013,c_1063,c_3137,c_3138,c_7755])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1510,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k8_setfam_1(X2,k1_xboole_0),k1_zfmisc_1(X2))
    | X0 != k8_setfam_1(X2,k1_xboole_0)
    | X1 != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_2518,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k8_setfam_1(X1,k1_xboole_0),k1_zfmisc_1(X1))
    | X0 != k8_setfam_1(X1,k1_xboole_0)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1510])).

cnf(c_6138,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k8_setfam_1(u1_struct_0(X1),k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))
    | X0 != k8_setfam_1(u1_struct_0(X1),k1_xboole_0)
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_2518])).

cnf(c_17644,plain,
    ( ~ m1_subset_1(k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))
    | sK1 != k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6138])).

cnf(c_17645,plain,
    ( k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))
    | sK1 != k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0)
    | m1_subset_1(k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17644])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_799,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1814,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1346,c_799])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_797,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1261,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_797])).

cnf(c_8553,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1814,c_1261])).

cnf(c_8554,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8553])).

cnf(c_8561,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(superposition,[status(thm)],[c_780,c_8554])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_791,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8801,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8561,c_791])).

cnf(c_7921,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8802,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8561,c_791])).

cnf(c_8837,plain,
    ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8802])).

cnf(c_9352,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8801,c_24,c_48,c_1013,c_7921,c_8837])).

cnf(c_9353,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 ),
    inference(renaming,[status(thm)],[c_9352])).

cnf(c_9359,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0) ),
    inference(equality_resolution,[status(thm)],[c_9353])).

cnf(c_27935,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9359,c_784])).

cnf(c_1136,plain,
    ( ~ v2_compts_1(sK1,X0)
    | v2_compts_1(sK1,X1)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1444,plain,
    ( v2_compts_1(sK1,X0)
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_1136])).

cnf(c_37527,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_1444])).

cnf(c_37528,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) = iProver_top
    | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37527])).

cnf(c_1300,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_39015,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_1300])).

cnf(c_39021,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39015])).

cnf(c_324,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2691,plain,
    ( X0 != u1_struct_0(X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_4461,plain,
    ( u1_struct_0(X0) != u1_struct_0(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2691])).

cnf(c_46773,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) != u1_struct_0(k1_pre_topc(sK0,sK1))
    | k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) = k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_4461])).

cnf(c_787,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_940,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X0,X2) = iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_787,c_789])).

cnf(c_3955,plain,
    ( v2_compts_1(u1_struct_0(X0),X0) != iProver_top
    | v2_compts_1(u1_struct_0(X0),X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_940])).

cnf(c_48388,plain,
    ( v2_compts_1(u1_struct_0(k1_pre_topc(sK0,sK1)),X0) = iProver_top
    | v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12657,c_3955])).

cnf(c_48535,plain,
    ( v2_compts_1(sK1,X0) = iProver_top
    | v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_48388,c_12657])).

cnf(c_48574,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) != iProver_top
    | v2_compts_1(sK1,sK0) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_48535])).

cnf(c_59577,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_58580,c_24,c_25,c_26,c_48,c_49,c_1013,c_1014,c_1053,c_1063,c_1120,c_1167,c_3084,c_3137,c_3138,c_3147,c_3165,c_4903,c_4904,c_5177,c_7755,c_9951,c_17645,c_27935,c_37528,c_39021,c_46773,c_48574])).

cnf(c_59579,plain,
    ( v2_compts_1(sK1,sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_59577])).

cnf(c_27966,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_27935])).

cnf(c_3256,plain,
    ( v2_compts_1(u1_struct_0(X0),X1) != iProver_top
    | v2_compts_1(u1_struct_0(X0),X0) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_928])).

cnf(c_26293,plain,
    ( v2_compts_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_pre_topc(sK0,sK1)) = iProver_top
    | v2_compts_1(sK1,X0) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12657,c_3256])).

cnf(c_26342,plain,
    ( v2_compts_1(sK1,X0) != iProver_top
    | v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_26293,c_12657])).

cnf(c_26356,plain,
    ( ~ v2_compts_1(sK1,X0)
    | v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
    | ~ l1_pre_topc(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_26342])).

cnf(c_26358,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ v2_compts_1(sK1,sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_26356])).

cnf(c_19,negated_conjecture,
    ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_67742,c_59579,c_46773,c_39015,c_27966,c_26358,c_17644,c_12657,c_9951,c_5174,c_4903,c_3165,c_3147,c_3084,c_1167,c_1119,c_1052,c_1013,c_48,c_19,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:03:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.34/2.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.34/2.51  
% 15.34/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.34/2.51  
% 15.34/2.51  ------  iProver source info
% 15.34/2.51  
% 15.34/2.51  git: date: 2020-06-30 10:37:57 +0100
% 15.34/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.34/2.51  git: non_committed_changes: false
% 15.34/2.51  git: last_make_outside_of_git: false
% 15.34/2.51  
% 15.34/2.51  ------ 
% 15.34/2.51  
% 15.34/2.51  ------ Input Options
% 15.34/2.51  
% 15.34/2.51  --out_options                           all
% 15.34/2.51  --tptp_safe_out                         true
% 15.34/2.51  --problem_path                          ""
% 15.34/2.51  --include_path                          ""
% 15.34/2.51  --clausifier                            res/vclausify_rel
% 15.34/2.51  --clausifier_options                    --mode clausify
% 15.34/2.51  --stdin                                 false
% 15.34/2.51  --stats_out                             all
% 15.34/2.51  
% 15.34/2.51  ------ General Options
% 15.34/2.51  
% 15.34/2.51  --fof                                   false
% 15.34/2.51  --time_out_real                         305.
% 15.34/2.51  --time_out_virtual                      -1.
% 15.34/2.51  --symbol_type_check                     false
% 15.34/2.51  --clausify_out                          false
% 15.34/2.51  --sig_cnt_out                           false
% 15.34/2.51  --trig_cnt_out                          false
% 15.34/2.51  --trig_cnt_out_tolerance                1.
% 15.34/2.51  --trig_cnt_out_sk_spl                   false
% 15.34/2.51  --abstr_cl_out                          false
% 15.34/2.51  
% 15.34/2.51  ------ Global Options
% 15.34/2.51  
% 15.34/2.51  --schedule                              default
% 15.34/2.51  --add_important_lit                     false
% 15.34/2.51  --prop_solver_per_cl                    1000
% 15.34/2.51  --min_unsat_core                        false
% 15.34/2.51  --soft_assumptions                      false
% 15.34/2.51  --soft_lemma_size                       3
% 15.34/2.51  --prop_impl_unit_size                   0
% 15.34/2.51  --prop_impl_unit                        []
% 15.34/2.51  --share_sel_clauses                     true
% 15.34/2.51  --reset_solvers                         false
% 15.34/2.51  --bc_imp_inh                            [conj_cone]
% 15.34/2.51  --conj_cone_tolerance                   3.
% 15.34/2.51  --extra_neg_conj                        none
% 15.34/2.51  --large_theory_mode                     true
% 15.34/2.51  --prolific_symb_bound                   200
% 15.34/2.51  --lt_threshold                          2000
% 15.34/2.51  --clause_weak_htbl                      true
% 15.34/2.51  --gc_record_bc_elim                     false
% 15.34/2.51  
% 15.34/2.51  ------ Preprocessing Options
% 15.34/2.51  
% 15.34/2.51  --preprocessing_flag                    true
% 15.34/2.51  --time_out_prep_mult                    0.1
% 15.34/2.51  --splitting_mode                        input
% 15.34/2.51  --splitting_grd                         true
% 15.34/2.51  --splitting_cvd                         false
% 15.34/2.51  --splitting_cvd_svl                     false
% 15.34/2.51  --splitting_nvd                         32
% 15.34/2.51  --sub_typing                            true
% 15.34/2.51  --prep_gs_sim                           true
% 15.34/2.51  --prep_unflatten                        true
% 15.34/2.51  --prep_res_sim                          true
% 15.34/2.51  --prep_upred                            true
% 15.34/2.51  --prep_sem_filter                       exhaustive
% 15.34/2.51  --prep_sem_filter_out                   false
% 15.34/2.51  --pred_elim                             true
% 15.34/2.51  --res_sim_input                         true
% 15.34/2.51  --eq_ax_congr_red                       true
% 15.34/2.51  --pure_diseq_elim                       true
% 15.34/2.51  --brand_transform                       false
% 15.34/2.51  --non_eq_to_eq                          false
% 15.34/2.51  --prep_def_merge                        true
% 15.34/2.51  --prep_def_merge_prop_impl              false
% 15.34/2.51  --prep_def_merge_mbd                    true
% 15.34/2.51  --prep_def_merge_tr_red                 false
% 15.34/2.51  --prep_def_merge_tr_cl                  false
% 15.34/2.51  --smt_preprocessing                     true
% 15.34/2.51  --smt_ac_axioms                         fast
% 15.34/2.51  --preprocessed_out                      false
% 15.34/2.51  --preprocessed_stats                    false
% 15.34/2.51  
% 15.34/2.51  ------ Abstraction refinement Options
% 15.34/2.51  
% 15.34/2.51  --abstr_ref                             []
% 15.34/2.51  --abstr_ref_prep                        false
% 15.34/2.51  --abstr_ref_until_sat                   false
% 15.34/2.51  --abstr_ref_sig_restrict                funpre
% 15.34/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.34/2.51  --abstr_ref_under                       []
% 15.34/2.51  
% 15.34/2.51  ------ SAT Options
% 15.34/2.51  
% 15.34/2.51  --sat_mode                              false
% 15.34/2.51  --sat_fm_restart_options                ""
% 15.34/2.51  --sat_gr_def                            false
% 15.34/2.51  --sat_epr_types                         true
% 15.34/2.51  --sat_non_cyclic_types                  false
% 15.34/2.51  --sat_finite_models                     false
% 15.34/2.51  --sat_fm_lemmas                         false
% 15.34/2.51  --sat_fm_prep                           false
% 15.34/2.51  --sat_fm_uc_incr                        true
% 15.34/2.51  --sat_out_model                         small
% 15.34/2.51  --sat_out_clauses                       false
% 15.34/2.51  
% 15.34/2.51  ------ QBF Options
% 15.34/2.51  
% 15.34/2.51  --qbf_mode                              false
% 15.34/2.51  --qbf_elim_univ                         false
% 15.34/2.51  --qbf_dom_inst                          none
% 15.34/2.51  --qbf_dom_pre_inst                      false
% 15.34/2.51  --qbf_sk_in                             false
% 15.34/2.51  --qbf_pred_elim                         true
% 15.34/2.51  --qbf_split                             512
% 15.34/2.51  
% 15.34/2.51  ------ BMC1 Options
% 15.34/2.51  
% 15.34/2.51  --bmc1_incremental                      false
% 15.34/2.51  --bmc1_axioms                           reachable_all
% 15.34/2.51  --bmc1_min_bound                        0
% 15.34/2.51  --bmc1_max_bound                        -1
% 15.34/2.51  --bmc1_max_bound_default                -1
% 15.34/2.51  --bmc1_symbol_reachability              true
% 15.34/2.51  --bmc1_property_lemmas                  false
% 15.34/2.51  --bmc1_k_induction                      false
% 15.34/2.51  --bmc1_non_equiv_states                 false
% 15.34/2.51  --bmc1_deadlock                         false
% 15.34/2.51  --bmc1_ucm                              false
% 15.34/2.51  --bmc1_add_unsat_core                   none
% 15.34/2.51  --bmc1_unsat_core_children              false
% 15.34/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.34/2.51  --bmc1_out_stat                         full
% 15.34/2.51  --bmc1_ground_init                      false
% 15.34/2.51  --bmc1_pre_inst_next_state              false
% 15.34/2.51  --bmc1_pre_inst_state                   false
% 15.34/2.51  --bmc1_pre_inst_reach_state             false
% 15.34/2.51  --bmc1_out_unsat_core                   false
% 15.34/2.51  --bmc1_aig_witness_out                  false
% 15.34/2.51  --bmc1_verbose                          false
% 15.34/2.51  --bmc1_dump_clauses_tptp                false
% 15.34/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.34/2.51  --bmc1_dump_file                        -
% 15.34/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.34/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.34/2.51  --bmc1_ucm_extend_mode                  1
% 15.34/2.51  --bmc1_ucm_init_mode                    2
% 15.34/2.51  --bmc1_ucm_cone_mode                    none
% 15.34/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.34/2.51  --bmc1_ucm_relax_model                  4
% 15.34/2.51  --bmc1_ucm_full_tr_after_sat            true
% 15.34/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 15.34/2.51  --bmc1_ucm_layered_model                none
% 15.34/2.51  --bmc1_ucm_max_lemma_size               10
% 15.34/2.51  
% 15.34/2.51  ------ AIG Options
% 15.34/2.51  
% 15.34/2.51  --aig_mode                              false
% 15.34/2.51  
% 15.34/2.51  ------ Instantiation Options
% 15.34/2.51  
% 15.34/2.51  --instantiation_flag                    true
% 15.34/2.51  --inst_sos_flag                         false
% 15.34/2.51  --inst_sos_phase                        true
% 15.34/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.34/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.34/2.51  --inst_lit_sel_side                     num_symb
% 15.34/2.51  --inst_solver_per_active                1400
% 15.34/2.51  --inst_solver_calls_frac                1.
% 15.34/2.51  --inst_passive_queue_type               priority_queues
% 15.34/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.34/2.51  --inst_passive_queues_freq              [25;2]
% 15.34/2.51  --inst_dismatching                      true
% 15.34/2.51  --inst_eager_unprocessed_to_passive     true
% 15.34/2.51  --inst_prop_sim_given                   true
% 15.34/2.51  --inst_prop_sim_new                     false
% 15.34/2.51  --inst_subs_new                         false
% 15.34/2.51  --inst_eq_res_simp                      false
% 15.34/2.51  --inst_subs_given                       false
% 15.34/2.51  --inst_orphan_elimination               true
% 15.34/2.51  --inst_learning_loop_flag               true
% 15.34/2.51  --inst_learning_start                   3000
% 15.34/2.51  --inst_learning_factor                  2
% 15.34/2.51  --inst_start_prop_sim_after_learn       3
% 15.34/2.51  --inst_sel_renew                        solver
% 15.34/2.51  --inst_lit_activity_flag                true
% 15.34/2.51  --inst_restr_to_given                   false
% 15.34/2.51  --inst_activity_threshold               500
% 15.34/2.51  --inst_out_proof                        true
% 15.34/2.51  
% 15.34/2.51  ------ Resolution Options
% 15.34/2.51  
% 15.34/2.51  --resolution_flag                       true
% 15.34/2.51  --res_lit_sel                           adaptive
% 15.34/2.51  --res_lit_sel_side                      none
% 15.34/2.51  --res_ordering                          kbo
% 15.34/2.51  --res_to_prop_solver                    active
% 15.34/2.51  --res_prop_simpl_new                    false
% 15.34/2.51  --res_prop_simpl_given                  true
% 15.34/2.51  --res_passive_queue_type                priority_queues
% 15.34/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.34/2.51  --res_passive_queues_freq               [15;5]
% 15.34/2.51  --res_forward_subs                      full
% 15.34/2.51  --res_backward_subs                     full
% 15.34/2.51  --res_forward_subs_resolution           true
% 15.34/2.51  --res_backward_subs_resolution          true
% 15.34/2.51  --res_orphan_elimination                true
% 15.34/2.51  --res_time_limit                        2.
% 15.34/2.51  --res_out_proof                         true
% 15.34/2.51  
% 15.34/2.51  ------ Superposition Options
% 15.34/2.51  
% 15.34/2.51  --superposition_flag                    true
% 15.34/2.51  --sup_passive_queue_type                priority_queues
% 15.34/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.34/2.51  --sup_passive_queues_freq               [8;1;4]
% 15.34/2.51  --demod_completeness_check              fast
% 15.34/2.51  --demod_use_ground                      true
% 15.34/2.51  --sup_to_prop_solver                    passive
% 15.34/2.51  --sup_prop_simpl_new                    true
% 15.34/2.51  --sup_prop_simpl_given                  true
% 15.34/2.51  --sup_fun_splitting                     false
% 15.34/2.51  --sup_smt_interval                      50000
% 15.34/2.51  
% 15.34/2.51  ------ Superposition Simplification Setup
% 15.34/2.51  
% 15.34/2.51  --sup_indices_passive                   []
% 15.34/2.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.34/2.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.34/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.34/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.34/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.34/2.51  --sup_full_bw                           [BwDemod]
% 15.34/2.51  --sup_immed_triv                        [TrivRules]
% 15.34/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.34/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.34/2.51  --sup_immed_bw_main                     []
% 15.34/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.34/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.34/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.34/2.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.34/2.51  
% 15.34/2.51  ------ Combination Options
% 15.34/2.51  
% 15.34/2.51  --comb_res_mult                         3
% 15.34/2.51  --comb_sup_mult                         2
% 15.34/2.51  --comb_inst_mult                        10
% 15.34/2.51  
% 15.34/2.51  ------ Debug Options
% 15.34/2.51  
% 15.34/2.51  --dbg_backtrace                         false
% 15.34/2.51  --dbg_dump_prop_clauses                 false
% 15.34/2.51  --dbg_dump_prop_clauses_file            -
% 15.34/2.51  --dbg_out_stat                          false
% 15.34/2.51  ------ Parsing...
% 15.34/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.34/2.51  
% 15.34/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.34/2.51  
% 15.34/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.34/2.51  
% 15.34/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.34/2.51  ------ Proving...
% 15.34/2.51  ------ Problem Properties 
% 15.34/2.51  
% 15.34/2.51  
% 15.34/2.51  clauses                                 25
% 15.34/2.51  conjectures                             6
% 15.34/2.51  EPR                                     2
% 15.34/2.51  Horn                                    20
% 15.34/2.51  unary                                   2
% 15.34/2.51  binary                                  9
% 15.34/2.51  lits                                    71
% 15.34/2.51  lits eq                                 9
% 15.34/2.51  fd_pure                                 0
% 15.34/2.51  fd_pseudo                               0
% 15.34/2.51  fd_cond                                 1
% 15.34/2.51  fd_pseudo_cond                          2
% 15.34/2.51  AC symbols                              0
% 15.34/2.51  
% 15.34/2.51  ------ Schedule dynamic 5 is on 
% 15.34/2.51  
% 15.34/2.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.34/2.51  
% 15.34/2.51  
% 15.34/2.51  ------ 
% 15.34/2.51  Current options:
% 15.34/2.51  ------ 
% 15.34/2.51  
% 15.34/2.51  ------ Input Options
% 15.34/2.51  
% 15.34/2.51  --out_options                           all
% 15.34/2.51  --tptp_safe_out                         true
% 15.34/2.51  --problem_path                          ""
% 15.34/2.51  --include_path                          ""
% 15.34/2.51  --clausifier                            res/vclausify_rel
% 15.34/2.51  --clausifier_options                    --mode clausify
% 15.34/2.51  --stdin                                 false
% 15.34/2.51  --stats_out                             all
% 15.34/2.51  
% 15.34/2.51  ------ General Options
% 15.34/2.51  
% 15.34/2.51  --fof                                   false
% 15.34/2.51  --time_out_real                         305.
% 15.34/2.51  --time_out_virtual                      -1.
% 15.34/2.51  --symbol_type_check                     false
% 15.34/2.51  --clausify_out                          false
% 15.34/2.51  --sig_cnt_out                           false
% 15.34/2.51  --trig_cnt_out                          false
% 15.34/2.51  --trig_cnt_out_tolerance                1.
% 15.34/2.51  --trig_cnt_out_sk_spl                   false
% 15.34/2.51  --abstr_cl_out                          false
% 15.34/2.51  
% 15.34/2.51  ------ Global Options
% 15.34/2.51  
% 15.34/2.51  --schedule                              default
% 15.34/2.51  --add_important_lit                     false
% 15.34/2.51  --prop_solver_per_cl                    1000
% 15.34/2.51  --min_unsat_core                        false
% 15.34/2.51  --soft_assumptions                      false
% 15.34/2.51  --soft_lemma_size                       3
% 15.34/2.51  --prop_impl_unit_size                   0
% 15.34/2.51  --prop_impl_unit                        []
% 15.34/2.51  --share_sel_clauses                     true
% 15.34/2.51  --reset_solvers                         false
% 15.34/2.51  --bc_imp_inh                            [conj_cone]
% 15.34/2.51  --conj_cone_tolerance                   3.
% 15.34/2.51  --extra_neg_conj                        none
% 15.34/2.51  --large_theory_mode                     true
% 15.34/2.51  --prolific_symb_bound                   200
% 15.34/2.51  --lt_threshold                          2000
% 15.34/2.51  --clause_weak_htbl                      true
% 15.34/2.51  --gc_record_bc_elim                     false
% 15.34/2.51  
% 15.34/2.51  ------ Preprocessing Options
% 15.34/2.51  
% 15.34/2.51  --preprocessing_flag                    true
% 15.34/2.51  --time_out_prep_mult                    0.1
% 15.34/2.51  --splitting_mode                        input
% 15.34/2.51  --splitting_grd                         true
% 15.34/2.51  --splitting_cvd                         false
% 15.34/2.51  --splitting_cvd_svl                     false
% 15.34/2.51  --splitting_nvd                         32
% 15.34/2.51  --sub_typing                            true
% 15.34/2.51  --prep_gs_sim                           true
% 15.34/2.51  --prep_unflatten                        true
% 15.34/2.51  --prep_res_sim                          true
% 15.34/2.51  --prep_upred                            true
% 15.34/2.51  --prep_sem_filter                       exhaustive
% 15.34/2.51  --prep_sem_filter_out                   false
% 15.34/2.51  --pred_elim                             true
% 15.34/2.51  --res_sim_input                         true
% 15.34/2.51  --eq_ax_congr_red                       true
% 15.34/2.51  --pure_diseq_elim                       true
% 15.34/2.51  --brand_transform                       false
% 15.34/2.51  --non_eq_to_eq                          false
% 15.34/2.51  --prep_def_merge                        true
% 15.34/2.51  --prep_def_merge_prop_impl              false
% 15.34/2.51  --prep_def_merge_mbd                    true
% 15.34/2.51  --prep_def_merge_tr_red                 false
% 15.34/2.51  --prep_def_merge_tr_cl                  false
% 15.34/2.51  --smt_preprocessing                     true
% 15.34/2.51  --smt_ac_axioms                         fast
% 15.34/2.51  --preprocessed_out                      false
% 15.34/2.51  --preprocessed_stats                    false
% 15.34/2.51  
% 15.34/2.51  ------ Abstraction refinement Options
% 15.34/2.51  
% 15.34/2.51  --abstr_ref                             []
% 15.34/2.51  --abstr_ref_prep                        false
% 15.34/2.51  --abstr_ref_until_sat                   false
% 15.34/2.51  --abstr_ref_sig_restrict                funpre
% 15.34/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.34/2.51  --abstr_ref_under                       []
% 15.34/2.51  
% 15.34/2.51  ------ SAT Options
% 15.34/2.51  
% 15.34/2.51  --sat_mode                              false
% 15.34/2.51  --sat_fm_restart_options                ""
% 15.34/2.51  --sat_gr_def                            false
% 15.34/2.51  --sat_epr_types                         true
% 15.34/2.51  --sat_non_cyclic_types                  false
% 15.34/2.51  --sat_finite_models                     false
% 15.34/2.51  --sat_fm_lemmas                         false
% 15.34/2.51  --sat_fm_prep                           false
% 15.34/2.51  --sat_fm_uc_incr                        true
% 15.34/2.51  --sat_out_model                         small
% 15.34/2.51  --sat_out_clauses                       false
% 15.34/2.51  
% 15.34/2.51  ------ QBF Options
% 15.34/2.51  
% 15.34/2.51  --qbf_mode                              false
% 15.34/2.51  --qbf_elim_univ                         false
% 15.34/2.51  --qbf_dom_inst                          none
% 15.34/2.51  --qbf_dom_pre_inst                      false
% 15.34/2.51  --qbf_sk_in                             false
% 15.34/2.51  --qbf_pred_elim                         true
% 15.34/2.51  --qbf_split                             512
% 15.34/2.51  
% 15.34/2.51  ------ BMC1 Options
% 15.34/2.51  
% 15.34/2.51  --bmc1_incremental                      false
% 15.34/2.51  --bmc1_axioms                           reachable_all
% 15.34/2.51  --bmc1_min_bound                        0
% 15.34/2.51  --bmc1_max_bound                        -1
% 15.34/2.51  --bmc1_max_bound_default                -1
% 15.34/2.51  --bmc1_symbol_reachability              true
% 15.34/2.51  --bmc1_property_lemmas                  false
% 15.34/2.51  --bmc1_k_induction                      false
% 15.34/2.51  --bmc1_non_equiv_states                 false
% 15.34/2.51  --bmc1_deadlock                         false
% 15.34/2.51  --bmc1_ucm                              false
% 15.34/2.51  --bmc1_add_unsat_core                   none
% 15.34/2.51  --bmc1_unsat_core_children              false
% 15.34/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.34/2.51  --bmc1_out_stat                         full
% 15.34/2.51  --bmc1_ground_init                      false
% 15.34/2.51  --bmc1_pre_inst_next_state              false
% 15.34/2.51  --bmc1_pre_inst_state                   false
% 15.34/2.51  --bmc1_pre_inst_reach_state             false
% 15.34/2.51  --bmc1_out_unsat_core                   false
% 15.34/2.51  --bmc1_aig_witness_out                  false
% 15.34/2.51  --bmc1_verbose                          false
% 15.34/2.51  --bmc1_dump_clauses_tptp                false
% 15.34/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.34/2.51  --bmc1_dump_file                        -
% 15.34/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.34/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.34/2.51  --bmc1_ucm_extend_mode                  1
% 15.34/2.51  --bmc1_ucm_init_mode                    2
% 15.34/2.51  --bmc1_ucm_cone_mode                    none
% 15.34/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.34/2.51  --bmc1_ucm_relax_model                  4
% 15.34/2.51  --bmc1_ucm_full_tr_after_sat            true
% 15.34/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 15.34/2.51  --bmc1_ucm_layered_model                none
% 15.34/2.51  --bmc1_ucm_max_lemma_size               10
% 15.34/2.51  
% 15.34/2.51  ------ AIG Options
% 15.34/2.51  
% 15.34/2.51  --aig_mode                              false
% 15.34/2.51  
% 15.34/2.51  ------ Instantiation Options
% 15.34/2.51  
% 15.34/2.51  --instantiation_flag                    true
% 15.34/2.51  --inst_sos_flag                         false
% 15.34/2.51  --inst_sos_phase                        true
% 15.34/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.34/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.34/2.51  --inst_lit_sel_side                     none
% 15.34/2.51  --inst_solver_per_active                1400
% 15.34/2.51  --inst_solver_calls_frac                1.
% 15.34/2.51  --inst_passive_queue_type               priority_queues
% 15.34/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.34/2.51  --inst_passive_queues_freq              [25;2]
% 15.34/2.51  --inst_dismatching                      true
% 15.34/2.51  --inst_eager_unprocessed_to_passive     true
% 15.34/2.51  --inst_prop_sim_given                   true
% 15.34/2.51  --inst_prop_sim_new                     false
% 15.34/2.51  --inst_subs_new                         false
% 15.34/2.51  --inst_eq_res_simp                      false
% 15.34/2.51  --inst_subs_given                       false
% 15.34/2.51  --inst_orphan_elimination               true
% 15.34/2.51  --inst_learning_loop_flag               true
% 15.34/2.51  --inst_learning_start                   3000
% 15.34/2.51  --inst_learning_factor                  2
% 15.34/2.51  --inst_start_prop_sim_after_learn       3
% 15.34/2.51  --inst_sel_renew                        solver
% 15.34/2.51  --inst_lit_activity_flag                true
% 15.34/2.51  --inst_restr_to_given                   false
% 15.34/2.51  --inst_activity_threshold               500
% 15.34/2.51  --inst_out_proof                        true
% 15.34/2.51  
% 15.34/2.51  ------ Resolution Options
% 15.34/2.51  
% 15.34/2.51  --resolution_flag                       false
% 15.34/2.51  --res_lit_sel                           adaptive
% 15.34/2.51  --res_lit_sel_side                      none
% 15.34/2.51  --res_ordering                          kbo
% 15.34/2.51  --res_to_prop_solver                    active
% 15.34/2.51  --res_prop_simpl_new                    false
% 15.34/2.51  --res_prop_simpl_given                  true
% 15.34/2.51  --res_passive_queue_type                priority_queues
% 15.34/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.34/2.51  --res_passive_queues_freq               [15;5]
% 15.34/2.51  --res_forward_subs                      full
% 15.34/2.51  --res_backward_subs                     full
% 15.34/2.51  --res_forward_subs_resolution           true
% 15.34/2.51  --res_backward_subs_resolution          true
% 15.34/2.51  --res_orphan_elimination                true
% 15.34/2.51  --res_time_limit                        2.
% 15.34/2.51  --res_out_proof                         true
% 15.34/2.51  
% 15.34/2.51  ------ Superposition Options
% 15.34/2.51  
% 15.34/2.51  --superposition_flag                    true
% 15.34/2.51  --sup_passive_queue_type                priority_queues
% 15.34/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.34/2.51  --sup_passive_queues_freq               [8;1;4]
% 15.34/2.51  --demod_completeness_check              fast
% 15.34/2.51  --demod_use_ground                      true
% 15.34/2.51  --sup_to_prop_solver                    passive
% 15.34/2.51  --sup_prop_simpl_new                    true
% 15.34/2.51  --sup_prop_simpl_given                  true
% 15.34/2.51  --sup_fun_splitting                     false
% 15.34/2.51  --sup_smt_interval                      50000
% 15.34/2.51  
% 15.34/2.51  ------ Superposition Simplification Setup
% 15.34/2.51  
% 15.34/2.51  --sup_indices_passive                   []
% 15.34/2.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.34/2.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.34/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.34/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.34/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.34/2.51  --sup_full_bw                           [BwDemod]
% 15.34/2.51  --sup_immed_triv                        [TrivRules]
% 15.34/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.34/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.34/2.51  --sup_immed_bw_main                     []
% 15.34/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.34/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.34/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.34/2.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.34/2.51  
% 15.34/2.51  ------ Combination Options
% 15.34/2.51  
% 15.34/2.51  --comb_res_mult                         3
% 15.34/2.51  --comb_sup_mult                         2
% 15.34/2.51  --comb_inst_mult                        10
% 15.34/2.51  
% 15.34/2.51  ------ Debug Options
% 15.34/2.51  
% 15.34/2.51  --dbg_backtrace                         false
% 15.34/2.51  --dbg_dump_prop_clauses                 false
% 15.34/2.51  --dbg_dump_prop_clauses_file            -
% 15.34/2.51  --dbg_out_stat                          false
% 15.34/2.51  
% 15.34/2.51  
% 15.34/2.51  
% 15.34/2.51  
% 15.34/2.51  ------ Proving...
% 15.34/2.51  
% 15.34/2.51  
% 15.34/2.51  % SZS status Theorem for theBenchmark.p
% 15.34/2.51  
% 15.34/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 15.34/2.51  
% 15.34/2.51  fof(f14,axiom,(
% 15.34/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 15.34/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.34/2.51  
% 15.34/2.51  fof(f33,plain,(
% 15.34/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.34/2.51    inference(ennf_transformation,[],[f14])).
% 15.34/2.51  
% 15.34/2.51  fof(f34,plain,(
% 15.34/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.34/2.51    inference(flattening,[],[f33])).
% 15.34/2.51  
% 15.34/2.51  fof(f37,plain,(
% 15.34/2.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1)) & (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.34/2.51    inference(nnf_transformation,[],[f34])).
% 15.34/2.51  
% 15.34/2.51  fof(f61,plain,(
% 15.34/2.51    ( ! [X2,X0,X3,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.34/2.51    inference(cnf_transformation,[],[f37])).
% 15.34/2.51  
% 15.34/2.51  fof(f69,plain,(
% 15.34/2.51    ( ! [X0,X3,X1] : (v2_compts_1(X3,X0) | ~v2_compts_1(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.34/2.51    inference(equality_resolution,[],[f61])).
% 15.34/2.51  
% 15.34/2.51  fof(f15,conjecture,(
% 15.34/2.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 15.34/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.34/2.51  
% 15.34/2.51  fof(f16,negated_conjecture,(
% 15.34/2.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 15.34/2.51    inference(negated_conjecture,[],[f15])).
% 15.34/2.51  
% 15.34/2.51  fof(f17,plain,(
% 15.34/2.51    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 15.34/2.51    inference(pure_predicate_removal,[],[f16])).
% 15.34/2.51  
% 15.34/2.51  fof(f18,plain,(
% 15.34/2.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 15.34/2.51    inference(pure_predicate_removal,[],[f17])).
% 15.34/2.51  
% 15.34/2.51  fof(f35,plain,(
% 15.34/2.51    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0))),
% 15.34/2.51    inference(ennf_transformation,[],[f18])).
% 15.34/2.51  
% 15.34/2.51  fof(f38,plain,(
% 15.34/2.51    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0))),
% 15.34/2.51    inference(nnf_transformation,[],[f35])).
% 15.34/2.51  
% 15.34/2.51  fof(f39,plain,(
% 15.34/2.51    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0))),
% 15.34/2.51    inference(flattening,[],[f38])).
% 15.34/2.51  
% 15.34/2.51  fof(f41,plain,(
% 15.34/2.51    ( ! [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) => ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(sK1,X0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(sK1,X0))))) )),
% 15.34/2.51    introduced(choice_axiom,[])).
% 15.34/2.51  
% 15.34/2.51  fof(f40,plain,(
% 15.34/2.51    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) & l1_pre_topc(sK0))),
% 15.34/2.51    introduced(choice_axiom,[])).
% 15.34/2.51  
% 15.34/2.51  fof(f42,plain,(
% 15.34/2.51    ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0)))) & l1_pre_topc(sK0)),
% 15.34/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 15.34/2.51  
% 15.34/2.51  fof(f63,plain,(
% 15.34/2.51    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,sK0)),
% 15.34/2.51    inference(cnf_transformation,[],[f42])).
% 15.34/2.51  
% 15.34/2.51  fof(f13,axiom,(
% 15.34/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 15.34/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.34/2.51  
% 15.34/2.51  fof(f32,plain,(
% 15.34/2.51    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 15.34/2.51    inference(ennf_transformation,[],[f13])).
% 15.34/2.51  
% 15.34/2.51  fof(f36,plain,(
% 15.34/2.51    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 15.34/2.51    inference(nnf_transformation,[],[f32])).
% 15.34/2.51  
% 15.34/2.51  fof(f58,plain,(
% 15.34/2.51    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 15.34/2.51    inference(cnf_transformation,[],[f36])).
% 15.34/2.51  
% 15.34/2.51  fof(f8,axiom,(
% 15.34/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 15.34/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.34/2.51  
% 15.34/2.51  fof(f27,plain,(
% 15.34/2.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.34/2.51    inference(ennf_transformation,[],[f8])).
% 15.34/2.51  
% 15.34/2.51  fof(f52,plain,(
% 15.34/2.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.34/2.51    inference(cnf_transformation,[],[f27])).
% 15.34/2.51  
% 15.34/2.51  fof(f62,plain,(
% 15.34/2.51    l1_pre_topc(sK0)),
% 15.34/2.51    inference(cnf_transformation,[],[f42])).
% 15.34/2.51  
% 15.34/2.51  fof(f1,axiom,(
% 15.34/2.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 15.34/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.34/2.51  
% 15.34/2.51  fof(f43,plain,(
% 15.34/2.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 15.34/2.51    inference(cnf_transformation,[],[f1])).
% 15.34/2.51  
% 15.34/2.51  fof(f11,axiom,(
% 15.34/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 15.34/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.34/2.51  
% 15.34/2.51  fof(f30,plain,(
% 15.34/2.51    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.34/2.51    inference(ennf_transformation,[],[f11])).
% 15.34/2.51  
% 15.34/2.51  fof(f56,plain,(
% 15.34/2.51    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.34/2.51    inference(cnf_transformation,[],[f30])).
% 15.34/2.51  
% 15.34/2.51  fof(f60,plain,(
% 15.34/2.51    ( ! [X2,X0,X3,X1] : (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.34/2.51    inference(cnf_transformation,[],[f37])).
% 15.34/2.51  
% 15.34/2.51  fof(f70,plain,(
% 15.34/2.51    ( ! [X0,X3,X1] : (v2_compts_1(X3,X1) | ~v2_compts_1(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.34/2.51    inference(equality_resolution,[],[f60])).
% 15.34/2.51  
% 15.34/2.51  fof(f12,axiom,(
% 15.34/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 15.34/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.34/2.51  
% 15.34/2.51  fof(f31,plain,(
% 15.34/2.51    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.34/2.51    inference(ennf_transformation,[],[f12])).
% 15.34/2.51  
% 15.34/2.51  fof(f57,plain,(
% 15.34/2.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.34/2.51    inference(cnf_transformation,[],[f31])).
% 15.34/2.51  
% 15.34/2.51  fof(f9,axiom,(
% 15.34/2.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.34/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.34/2.51  
% 15.34/2.51  fof(f28,plain,(
% 15.34/2.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.34/2.51    inference(ennf_transformation,[],[f9])).
% 15.34/2.51  
% 15.34/2.51  fof(f53,plain,(
% 15.34/2.51    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 15.34/2.51    inference(cnf_transformation,[],[f28])).
% 15.34/2.51  
% 15.34/2.51  fof(f6,axiom,(
% 15.34/2.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 15.34/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.34/2.51  
% 15.34/2.51  fof(f24,plain,(
% 15.34/2.51    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 15.34/2.51    inference(ennf_transformation,[],[f6])).
% 15.34/2.51  
% 15.34/2.51  fof(f49,plain,(
% 15.34/2.51    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 15.34/2.51    inference(cnf_transformation,[],[f24])).
% 15.34/2.51  
% 15.34/2.51  fof(f7,axiom,(
% 15.34/2.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 15.34/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.34/2.51  
% 15.34/2.51  fof(f25,plain,(
% 15.34/2.51    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 15.34/2.51    inference(ennf_transformation,[],[f7])).
% 15.34/2.51  
% 15.34/2.51  fof(f26,plain,(
% 15.34/2.51    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 15.34/2.51    inference(flattening,[],[f25])).
% 15.34/2.51  
% 15.34/2.51  fof(f51,plain,(
% 15.34/2.51    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.34/2.51    inference(cnf_transformation,[],[f26])).
% 15.34/2.51  
% 15.34/2.51  fof(f2,axiom,(
% 15.34/2.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 15.34/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.34/2.51  
% 15.34/2.51  fof(f20,plain,(
% 15.34/2.51    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 15.34/2.51    inference(ennf_transformation,[],[f2])).
% 15.34/2.51  
% 15.34/2.51  fof(f45,plain,(
% 15.34/2.51    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 15.34/2.51    inference(cnf_transformation,[],[f20])).
% 15.34/2.51  
% 15.34/2.51  fof(f68,plain,(
% 15.34/2.51    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 15.34/2.51    inference(equality_resolution,[],[f45])).
% 15.34/2.51  
% 15.34/2.51  fof(f3,axiom,(
% 15.34/2.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 15.34/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.34/2.51  
% 15.34/2.51  fof(f21,plain,(
% 15.34/2.51    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 15.34/2.51    inference(ennf_transformation,[],[f3])).
% 15.34/2.51  
% 15.34/2.51  fof(f46,plain,(
% 15.34/2.51    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 15.34/2.51    inference(cnf_transformation,[],[f21])).
% 15.34/2.51  
% 15.34/2.51  fof(f66,plain,(
% 15.34/2.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.34/2.51    inference(cnf_transformation,[],[f42])).
% 15.34/2.51  
% 15.34/2.51  fof(f59,plain,(
% 15.34/2.51    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 15.34/2.51    inference(cnf_transformation,[],[f36])).
% 15.34/2.51  
% 15.34/2.51  fof(f5,axiom,(
% 15.34/2.51    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 15.34/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.34/2.51  
% 15.34/2.51  fof(f22,plain,(
% 15.34/2.51    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 15.34/2.51    inference(ennf_transformation,[],[f5])).
% 15.34/2.51  
% 15.34/2.51  fof(f23,plain,(
% 15.34/2.51    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 15.34/2.51    inference(flattening,[],[f22])).
% 15.34/2.51  
% 15.34/2.51  fof(f47,plain,(
% 15.34/2.51    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 15.34/2.51    inference(cnf_transformation,[],[f23])).
% 15.34/2.51  
% 15.34/2.51  fof(f48,plain,(
% 15.34/2.51    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 15.34/2.51    inference(cnf_transformation,[],[f24])).
% 15.34/2.51  
% 15.34/2.51  fof(f10,axiom,(
% 15.34/2.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 15.34/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.34/2.51  
% 15.34/2.51  fof(f29,plain,(
% 15.34/2.51    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 15.34/2.51    inference(ennf_transformation,[],[f10])).
% 15.34/2.51  
% 15.34/2.51  fof(f54,plain,(
% 15.34/2.51    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 15.34/2.51    inference(cnf_transformation,[],[f29])).
% 15.34/2.51  
% 15.34/2.51  fof(f67,plain,(
% 15.34/2.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)),
% 15.34/2.51    inference(cnf_transformation,[],[f42])).
% 15.34/2.51  
% 15.34/2.51  cnf(c_17,plain,
% 15.34/2.51      ( ~ v2_compts_1(X0,X1)
% 15.34/2.51      | v2_compts_1(X0,X2)
% 15.34/2.51      | ~ m1_pre_topc(X1,X2)
% 15.34/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 15.34/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.34/2.51      | ~ l1_pre_topc(X2) ),
% 15.34/2.51      inference(cnf_transformation,[],[f69]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1137,plain,
% 15.34/2.51      ( ~ v2_compts_1(sK1,X0)
% 15.34/2.51      | v2_compts_1(sK1,X1)
% 15.34/2.51      | ~ m1_pre_topc(X0,X1)
% 15.34/2.51      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 15.34/2.51      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
% 15.34/2.51      | ~ l1_pre_topc(X1) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_17]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_3550,plain,
% 15.34/2.51      ( ~ v2_compts_1(sK1,X0)
% 15.34/2.51      | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 15.34/2.51      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 15.34/2.51      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 15.34/2.51      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 15.34/2.51      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_1137]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_67742,plain,
% 15.34/2.51      ( ~ v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
% 15.34/2.51      | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 15.34/2.51      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 15.34/2.51      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
% 15.34/2.51      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 15.34/2.51      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_3550]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_23,negated_conjecture,
% 15.34/2.51      ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 15.34/2.51      | v2_compts_1(sK1,sK0) ),
% 15.34/2.51      inference(cnf_transformation,[],[f63]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_781,plain,
% 15.34/2.51      ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 15.34/2.51      | v2_compts_1(sK1,sK0) = iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_16,plain,
% 15.34/2.51      ( ~ m1_pre_topc(X0,X1)
% 15.34/2.51      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.34/2.51      | ~ l1_pre_topc(X0)
% 15.34/2.51      | ~ l1_pre_topc(X1) ),
% 15.34/2.51      inference(cnf_transformation,[],[f58]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_9,plain,
% 15.34/2.51      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 15.34/2.51      inference(cnf_transformation,[],[f52]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_137,plain,
% 15.34/2.51      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.34/2.51      | ~ m1_pre_topc(X0,X1)
% 15.34/2.51      | ~ l1_pre_topc(X1) ),
% 15.34/2.51      inference(global_propositional_subsumption,
% 15.34/2.51                [status(thm)],
% 15.34/2.51                [c_16,c_9]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_138,plain,
% 15.34/2.51      ( ~ m1_pre_topc(X0,X1)
% 15.34/2.51      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.34/2.51      | ~ l1_pre_topc(X1) ),
% 15.34/2.51      inference(renaming,[status(thm)],[c_137]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_779,plain,
% 15.34/2.51      ( m1_pre_topc(X0,X1) != iProver_top
% 15.34/2.51      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 15.34/2.51      | l1_pre_topc(X1) != iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_138]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_24,negated_conjecture,
% 15.34/2.51      ( l1_pre_topc(sK0) ),
% 15.34/2.51      inference(cnf_transformation,[],[f62]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_780,plain,
% 15.34/2.51      ( l1_pre_topc(sK0) = iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_0,plain,
% 15.34/2.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 15.34/2.51      inference(cnf_transformation,[],[f43]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_803,plain,
% 15.34/2.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_13,plain,
% 15.34/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.34/2.51      | ~ l1_pre_topc(X1)
% 15.34/2.51      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 15.34/2.51      inference(cnf_transformation,[],[f56]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_790,plain,
% 15.34/2.51      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
% 15.34/2.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.34/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1932,plain,
% 15.34/2.51      ( u1_struct_0(k1_pre_topc(X0,k1_xboole_0)) = k1_xboole_0
% 15.34/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_803,c_790]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_3349,plain,
% 15.34/2.51      ( u1_struct_0(k1_pre_topc(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_780,c_1932]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_18,plain,
% 15.34/2.51      ( ~ v2_compts_1(X0,X1)
% 15.34/2.51      | v2_compts_1(X0,X2)
% 15.34/2.51      | ~ m1_pre_topc(X2,X1)
% 15.34/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.34/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 15.34/2.51      | ~ l1_pre_topc(X1) ),
% 15.34/2.51      inference(cnf_transformation,[],[f70]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_786,plain,
% 15.34/2.51      ( v2_compts_1(X0,X1) != iProver_top
% 15.34/2.51      | v2_compts_1(X0,X2) = iProver_top
% 15.34/2.51      | m1_pre_topc(X2,X1) != iProver_top
% 15.34/2.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.34/2.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 15.34/2.51      | l1_pre_topc(X1) != iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_14,plain,
% 15.34/2.51      ( ~ m1_pre_topc(X0,X1)
% 15.34/2.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 15.34/2.51      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.34/2.51      | ~ l1_pre_topc(X1) ),
% 15.34/2.51      inference(cnf_transformation,[],[f57]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_789,plain,
% 15.34/2.51      ( m1_pre_topc(X0,X1) != iProver_top
% 15.34/2.51      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.34/2.51      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 15.34/2.51      | l1_pre_topc(X1) != iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_928,plain,
% 15.34/2.51      ( v2_compts_1(X0,X1) != iProver_top
% 15.34/2.51      | v2_compts_1(X0,X2) = iProver_top
% 15.34/2.51      | m1_pre_topc(X2,X1) != iProver_top
% 15.34/2.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 15.34/2.51      | l1_pre_topc(X1) != iProver_top ),
% 15.34/2.51      inference(forward_subsumption_resolution,
% 15.34/2.51                [status(thm)],
% 15.34/2.51                [c_786,c_789]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_3442,plain,
% 15.34/2.51      ( v2_compts_1(X0,X1) != iProver_top
% 15.34/2.51      | v2_compts_1(X0,k1_pre_topc(sK0,k1_xboole_0)) = iProver_top
% 15.34/2.51      | m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),X1) != iProver_top
% 15.34/2.51      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.34/2.51      | l1_pre_topc(X1) != iProver_top ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_3349,c_928]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_4505,plain,
% 15.34/2.51      ( v2_compts_1(X0,k1_pre_topc(sK0,k1_xboole_0)) = iProver_top
% 15.34/2.51      | v2_compts_1(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 15.34/2.51      | m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),X1) != iProver_top
% 15.34/2.51      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.34/2.51      | l1_pre_topc(X1) != iProver_top
% 15.34/2.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_779,c_3442]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_10,plain,
% 15.34/2.51      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 15.34/2.51      | ~ l1_pre_topc(X0) ),
% 15.34/2.51      inference(cnf_transformation,[],[f53]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_793,plain,
% 15.34/2.51      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 15.34/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_5,plain,
% 15.34/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 15.34/2.51      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 15.34/2.51      inference(cnf_transformation,[],[f49]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_798,plain,
% 15.34/2.51      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 15.34/2.51      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1346,plain,
% 15.34/2.51      ( l1_pre_topc(X0) != iProver_top
% 15.34/2.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_793,c_798]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_58575,plain,
% 15.34/2.51      ( v2_compts_1(X0,k1_pre_topc(sK0,k1_xboole_0)) = iProver_top
% 15.34/2.51      | v2_compts_1(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 15.34/2.51      | m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),X1) != iProver_top
% 15.34/2.51      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.34/2.51      | l1_pre_topc(X1) != iProver_top ),
% 15.34/2.51      inference(forward_subsumption_resolution,
% 15.34/2.51                [status(thm)],
% 15.34/2.51                [c_4505,c_1346]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_58580,plain,
% 15.34/2.51      ( v2_compts_1(sK1,k1_pre_topc(sK0,k1_xboole_0)) = iProver_top
% 15.34/2.51      | v2_compts_1(sK1,sK0) = iProver_top
% 15.34/2.51      | m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),sK0) != iProver_top
% 15.34/2.51      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.34/2.51      | l1_pre_topc(sK0) != iProver_top ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_781,c_58575]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_25,plain,
% 15.34/2.51      ( l1_pre_topc(sK0) = iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_26,plain,
% 15.34/2.51      ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 15.34/2.51      | v2_compts_1(sK1,sK0) = iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_47,plain,
% 15.34/2.51      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 15.34/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_49,plain,
% 15.34/2.51      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 15.34/2.51      | l1_pre_topc(sK0) != iProver_top ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_47]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1011,plain,
% 15.34/2.51      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 15.34/2.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_5]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1012,plain,
% 15.34/2.51      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 15.34/2.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_1011]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1014,plain,
% 15.34/2.51      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 15.34/2.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_1012]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_7,plain,
% 15.34/2.51      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 15.34/2.51      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 15.34/2.51      | ~ l1_pre_topc(X0) ),
% 15.34/2.51      inference(cnf_transformation,[],[f51]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1052,plain,
% 15.34/2.51      ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
% 15.34/2.51      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.34/2.51      | ~ l1_pre_topc(sK0) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_7]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1053,plain,
% 15.34/2.51      ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top
% 15.34/2.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.34/2.51      | l1_pre_topc(sK0) != iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_1052]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1119,plain,
% 15.34/2.51      ( m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 15.34/2.51      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
% 15.34/2.51      | ~ l1_pre_topc(sK0) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_138]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1120,plain,
% 15.34/2.51      ( m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 15.34/2.51      | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) != iProver_top
% 15.34/2.51      | l1_pre_topc(sK0) != iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_1119]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_322,plain,( X0 = X0 ),theory(equality) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1167,plain,
% 15.34/2.51      ( sK1 = sK1 ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_322]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_323,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1429,plain,
% 15.34/2.51      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_323]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_2157,plain,
% 15.34/2.51      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_1429]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_3084,plain,
% 15.34/2.51      ( u1_struct_0(k1_pre_topc(sK0,sK1)) != sK1
% 15.34/2.51      | sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
% 15.34/2.51      | sK1 != sK1 ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_2157]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1,plain,
% 15.34/2.51      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 15.34/2.51      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 15.34/2.51      inference(cnf_transformation,[],[f68]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_3147,plain,
% 15.34/2.51      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))))
% 15.34/2.51      | k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0) = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_1]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_3165,plain,
% 15.34/2.51      ( u1_struct_0(k1_pre_topc(sK0,sK1)) = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_322]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1002,plain,
% 15.34/2.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_0]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_2289,plain,
% 15.34/2.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_1002]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_4903,plain,
% 15.34/2.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_2289]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_4904,plain,
% 15.34/2.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))) = iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_4903]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_3,plain,
% 15.34/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 15.34/2.51      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 15.34/2.51      inference(cnf_transformation,[],[f46]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1198,plain,
% 15.34/2.51      ( m1_subset_1(k8_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(X0))
% 15.34/2.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_3]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1499,plain,
% 15.34/2.51      ( m1_subset_1(k8_setfam_1(u1_struct_0(X0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
% 15.34/2.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_1198]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_5174,plain,
% 15.34/2.51      ( m1_subset_1(k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
% 15.34/2.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_1499]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_5177,plain,
% 15.34/2.51      ( m1_subset_1(k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) = iProver_top
% 15.34/2.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))) != iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_5174]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_3332,plain,
% 15.34/2.51      ( X0 != u1_struct_0(k1_pre_topc(sK0,sK1))
% 15.34/2.51      | sK1 = X0
% 15.34/2.51      | sK1 != u1_struct_0(k1_pre_topc(sK0,sK1)) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_1429]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_9951,plain,
% 15.34/2.51      ( k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0) != u1_struct_0(k1_pre_topc(sK0,sK1))
% 15.34/2.51      | sK1 = k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0)
% 15.34/2.51      | sK1 != u1_struct_0(k1_pre_topc(sK0,sK1)) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_3332]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_20,negated_conjecture,
% 15.34/2.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 15.34/2.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.34/2.51      inference(cnf_transformation,[],[f66]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_784,plain,
% 15.34/2.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
% 15.34/2.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1934,plain,
% 15.34/2.51      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
% 15.34/2.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 15.34/2.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_784,c_790]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_2166,plain,
% 15.34/2.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 15.34/2.51      | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
% 15.34/2.51      inference(global_propositional_subsumption,
% 15.34/2.51                [status(thm)],
% 15.34/2.51                [c_1934,c_25,c_49,c_1014]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_2167,plain,
% 15.34/2.51      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
% 15.34/2.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.34/2.51      inference(renaming,[status(thm)],[c_2166]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_2172,plain,
% 15.34/2.51      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
% 15.34/2.51      | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
% 15.34/2.51      | l1_pre_topc(sK0) != iProver_top ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_2167,c_790]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_2175,plain,
% 15.34/2.51      ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
% 15.34/2.51      | u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
% 15.34/2.51      inference(global_propositional_subsumption,
% 15.34/2.51                [status(thm)],
% 15.34/2.51                [c_2172,c_25]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_2176,plain,
% 15.34/2.51      ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
% 15.34/2.51      | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
% 15.34/2.51      inference(renaming,[status(thm)],[c_2175]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_15,plain,
% 15.34/2.51      ( m1_pre_topc(X0,X1)
% 15.34/2.51      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.34/2.51      | ~ l1_pre_topc(X0)
% 15.34/2.51      | ~ l1_pre_topc(X1) ),
% 15.34/2.51      inference(cnf_transformation,[],[f59]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_788,plain,
% 15.34/2.51      ( m1_pre_topc(X0,X1) = iProver_top
% 15.34/2.51      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 15.34/2.51      | l1_pre_topc(X1) != iProver_top
% 15.34/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_2183,plain,
% 15.34/2.51      ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
% 15.34/2.51      | m1_pre_topc(X0,k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
% 15.34/2.51      | m1_pre_topc(X0,g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))) != iProver_top
% 15.34/2.51      | l1_pre_topc(X0) != iProver_top
% 15.34/2.51      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_2176,c_788]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_48,plain,
% 15.34/2.51      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 15.34/2.51      | ~ l1_pre_topc(sK0) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_10]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1013,plain,
% 15.34/2.51      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 15.34/2.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_1011]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1063,plain,
% 15.34/2.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.34/2.51      | ~ l1_pre_topc(sK0)
% 15.34/2.51      | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_13]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_796,plain,
% 15.34/2.51      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 15.34/2.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.34/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_2787,plain,
% 15.34/2.51      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 15.34/2.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 15.34/2.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_784,c_796]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_3115,plain,
% 15.34/2.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 15.34/2.51      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 15.34/2.51      inference(global_propositional_subsumption,
% 15.34/2.51                [status(thm)],
% 15.34/2.51                [c_2787,c_25,c_49,c_1014]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_3116,plain,
% 15.34/2.51      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 15.34/2.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.34/2.51      inference(renaming,[status(thm)],[c_3115]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_794,plain,
% 15.34/2.51      ( m1_pre_topc(X0,X1) != iProver_top
% 15.34/2.51      | l1_pre_topc(X1) != iProver_top
% 15.34/2.51      | l1_pre_topc(X0) = iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_3121,plain,
% 15.34/2.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 15.34/2.51      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
% 15.34/2.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_3116,c_794]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_3137,plain,
% 15.34/2.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.34/2.51      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
% 15.34/2.51      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 15.34/2.51      inference(predicate_to_equality_rev,[status(thm)],[c_3121]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_3122,plain,
% 15.34/2.51      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) = iProver_top
% 15.34/2.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 15.34/2.51      | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top
% 15.34/2.51      | l1_pre_topc(sK0) != iProver_top ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_3116,c_788]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_3138,plain,
% 15.34/2.51      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
% 15.34/2.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.34/2.51      | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
% 15.34/2.51      | ~ l1_pre_topc(sK0) ),
% 15.34/2.51      inference(predicate_to_equality_rev,[status(thm)],[c_3122]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_802,plain,
% 15.34/2.51      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 15.34/2.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_810,plain,
% 15.34/2.51      ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 15.34/2.51      inference(forward_subsumption_resolution,
% 15.34/2.51                [status(thm)],
% 15.34/2.51                [c_802,c_803]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_800,plain,
% 15.34/2.51      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 15.34/2.51      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1667,plain,
% 15.34/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
% 15.34/2.51      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_810,c_800]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1007,plain,
% 15.34/2.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_1002]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1739,plain,
% 15.34/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.34/2.51      inference(global_propositional_subsumption,
% 15.34/2.51                [status(thm)],
% 15.34/2.51                [c_1667,c_1007]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_2588,plain,
% 15.34/2.51      ( m1_pre_topc(X0,X1) != iProver_top
% 15.34/2.51      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 15.34/2.51      | l1_pre_topc(X1) != iProver_top ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_1739,c_789]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_7623,plain,
% 15.34/2.51      ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
% 15.34/2.51      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) != iProver_top
% 15.34/2.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 15.34/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_2176,c_2588]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_7753,plain,
% 15.34/2.51      ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
% 15.34/2.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 15.34/2.51      | ~ l1_pre_topc(X0)
% 15.34/2.51      | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
% 15.34/2.51      inference(predicate_to_equality_rev,[status(thm)],[c_7623]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_7755,plain,
% 15.34/2.51      ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
% 15.34/2.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.34/2.51      | ~ l1_pre_topc(sK0)
% 15.34/2.51      | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_7753]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_12657,plain,
% 15.34/2.51      ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
% 15.34/2.51      inference(global_propositional_subsumption,
% 15.34/2.51                [status(thm)],
% 15.34/2.51                [c_2183,c_24,c_48,c_1013,c_1063,c_3137,c_3138,c_7755]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_325,plain,
% 15.34/2.51      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.34/2.51      theory(equality) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1510,plain,
% 15.34/2.51      ( m1_subset_1(X0,X1)
% 15.34/2.51      | ~ m1_subset_1(k8_setfam_1(X2,k1_xboole_0),k1_zfmisc_1(X2))
% 15.34/2.51      | X0 != k8_setfam_1(X2,k1_xboole_0)
% 15.34/2.51      | X1 != k1_zfmisc_1(X2) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_325]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_2518,plain,
% 15.34/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.34/2.51      | ~ m1_subset_1(k8_setfam_1(X1,k1_xboole_0),k1_zfmisc_1(X1))
% 15.34/2.51      | X0 != k8_setfam_1(X1,k1_xboole_0)
% 15.34/2.51      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_1510]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_6138,plain,
% 15.34/2.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.34/2.51      | ~ m1_subset_1(k8_setfam_1(u1_struct_0(X1),k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.34/2.51      | X0 != k8_setfam_1(u1_struct_0(X1),k1_xboole_0)
% 15.34/2.51      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_2518]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_17644,plain,
% 15.34/2.51      ( ~ m1_subset_1(k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
% 15.34/2.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
% 15.34/2.51      | k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))
% 15.34/2.51      | sK1 != k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_6138]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_17645,plain,
% 15.34/2.51      ( k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) != k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))
% 15.34/2.51      | sK1 != k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0)
% 15.34/2.51      | m1_subset_1(k8_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_xboole_0),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) != iProver_top
% 15.34/2.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) = iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_17644]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_4,plain,
% 15.34/2.51      ( ~ l1_pre_topc(X0)
% 15.34/2.51      | ~ v1_pre_topc(X0)
% 15.34/2.51      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 15.34/2.51      inference(cnf_transformation,[],[f47]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_799,plain,
% 15.34/2.51      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 15.34/2.51      | l1_pre_topc(X0) != iProver_top
% 15.34/2.51      | v1_pre_topc(X0) != iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1814,plain,
% 15.34/2.51      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 15.34/2.51      | l1_pre_topc(X0) != iProver_top
% 15.34/2.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_1346,c_799]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_6,plain,
% 15.34/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 15.34/2.51      | v1_pre_topc(g1_pre_topc(X1,X0)) ),
% 15.34/2.51      inference(cnf_transformation,[],[f48]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_797,plain,
% 15.34/2.51      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 15.34/2.51      | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_1261,plain,
% 15.34/2.51      ( l1_pre_topc(X0) != iProver_top
% 15.34/2.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_793,c_797]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_8553,plain,
% 15.34/2.51      ( l1_pre_topc(X0) != iProver_top
% 15.34/2.51      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 15.34/2.51      inference(global_propositional_subsumption,
% 15.34/2.51                [status(thm)],
% 15.34/2.51                [c_1814,c_1261]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_8554,plain,
% 15.34/2.51      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 15.34/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.34/2.51      inference(renaming,[status(thm)],[c_8553]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_8561,plain,
% 15.34/2.51      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_780,c_8554]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_12,plain,
% 15.34/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 15.34/2.51      | X2 = X1
% 15.34/2.51      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 15.34/2.51      inference(cnf_transformation,[],[f54]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_791,plain,
% 15.34/2.51      ( X0 = X1
% 15.34/2.51      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 15.34/2.51      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 15.34/2.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_8801,plain,
% 15.34/2.51      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
% 15.34/2.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
% 15.34/2.51      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 15.34/2.51      inference(superposition,[status(thm)],[c_8561,c_791]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_7921,plain,
% 15.34/2.51      ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 15.34/2.51      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 15.34/2.51      inference(instantiation,[status(thm)],[c_10]) ).
% 15.34/2.51  
% 15.34/2.51  cnf(c_8802,plain,
% 15.34/2.51      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
% 15.34/2.52      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
% 15.34/2.52      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top ),
% 15.34/2.52      inference(superposition,[status(thm)],[c_8561,c_791]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_8837,plain,
% 15.34/2.52      ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 15.34/2.52      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
% 15.34/2.52      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 ),
% 15.34/2.52      inference(predicate_to_equality_rev,[status(thm)],[c_8802]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_9352,plain,
% 15.34/2.52      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
% 15.34/2.52      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1) ),
% 15.34/2.52      inference(global_propositional_subsumption,
% 15.34/2.52                [status(thm)],
% 15.34/2.52                [c_8801,c_24,c_48,c_1013,c_7921,c_8837]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_9353,plain,
% 15.34/2.52      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X0,X1)
% 15.34/2.52      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 ),
% 15.34/2.52      inference(renaming,[status(thm)],[c_9352]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_9359,plain,
% 15.34/2.52      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_struct_0(sK0) ),
% 15.34/2.52      inference(equality_resolution,[status(thm)],[c_9353]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_27935,plain,
% 15.34/2.52      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.34/2.52      inference(demodulation,[status(thm)],[c_9359,c_784]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_1136,plain,
% 15.34/2.52      ( ~ v2_compts_1(sK1,X0)
% 15.34/2.52      | v2_compts_1(sK1,X1)
% 15.34/2.52      | ~ m1_pre_topc(X1,X0)
% 15.34/2.52      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 15.34/2.52      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
% 15.34/2.52      | ~ l1_pre_topc(X0) ),
% 15.34/2.52      inference(instantiation,[status(thm)],[c_18]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_1444,plain,
% 15.34/2.52      ( v2_compts_1(sK1,X0)
% 15.34/2.52      | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 15.34/2.52      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 15.34/2.52      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 15.34/2.52      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 15.34/2.52      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 15.34/2.52      inference(instantiation,[status(thm)],[c_1136]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_37527,plain,
% 15.34/2.52      ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
% 15.34/2.52      | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 15.34/2.52      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 15.34/2.52      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
% 15.34/2.52      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 15.34/2.52      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 15.34/2.52      inference(instantiation,[status(thm)],[c_1444]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_37528,plain,
% 15.34/2.52      ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) = iProver_top
% 15.34/2.52      | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 15.34/2.52      | m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 15.34/2.52      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) != iProver_top
% 15.34/2.52      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
% 15.34/2.52      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 15.34/2.52      inference(predicate_to_equality,[status(thm)],[c_37527]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_1300,plain,
% 15.34/2.52      ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 15.34/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
% 15.34/2.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 15.34/2.52      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 15.34/2.52      inference(instantiation,[status(thm)],[c_14]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_39015,plain,
% 15.34/2.52      ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 15.34/2.52      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
% 15.34/2.52      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 15.34/2.52      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 15.34/2.52      inference(instantiation,[status(thm)],[c_1300]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_39021,plain,
% 15.34/2.52      ( m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 15.34/2.52      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) != iProver_top
% 15.34/2.52      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top
% 15.34/2.52      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
% 15.34/2.52      inference(predicate_to_equality,[status(thm)],[c_39015]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_324,plain,
% 15.34/2.52      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 15.34/2.52      theory(equality) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_2691,plain,
% 15.34/2.52      ( X0 != u1_struct_0(X1)
% 15.34/2.52      | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(X1)) ),
% 15.34/2.52      inference(instantiation,[status(thm)],[c_324]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_4461,plain,
% 15.34/2.52      ( u1_struct_0(X0) != u1_struct_0(X0)
% 15.34/2.52      | k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(X0)) ),
% 15.34/2.52      inference(instantiation,[status(thm)],[c_2691]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_46773,plain,
% 15.34/2.52      ( u1_struct_0(k1_pre_topc(sK0,sK1)) != u1_struct_0(k1_pre_topc(sK0,sK1))
% 15.34/2.52      | k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) = k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))) ),
% 15.34/2.52      inference(instantiation,[status(thm)],[c_4461]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_787,plain,
% 15.34/2.52      ( v2_compts_1(X0,X1) != iProver_top
% 15.34/2.52      | v2_compts_1(X0,X2) = iProver_top
% 15.34/2.52      | m1_pre_topc(X1,X2) != iProver_top
% 15.34/2.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.34/2.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 15.34/2.52      | l1_pre_topc(X2) != iProver_top ),
% 15.34/2.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_940,plain,
% 15.34/2.52      ( v2_compts_1(X0,X1) != iProver_top
% 15.34/2.52      | v2_compts_1(X0,X2) = iProver_top
% 15.34/2.52      | m1_pre_topc(X1,X2) != iProver_top
% 15.34/2.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.34/2.52      | l1_pre_topc(X2) != iProver_top ),
% 15.34/2.52      inference(forward_subsumption_resolution,
% 15.34/2.52                [status(thm)],
% 15.34/2.52                [c_787,c_789]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_3955,plain,
% 15.34/2.52      ( v2_compts_1(u1_struct_0(X0),X0) != iProver_top
% 15.34/2.52      | v2_compts_1(u1_struct_0(X0),X1) = iProver_top
% 15.34/2.52      | m1_pre_topc(X0,X1) != iProver_top
% 15.34/2.52      | l1_pre_topc(X1) != iProver_top ),
% 15.34/2.52      inference(superposition,[status(thm)],[c_1739,c_940]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_48388,plain,
% 15.34/2.52      ( v2_compts_1(u1_struct_0(k1_pre_topc(sK0,sK1)),X0) = iProver_top
% 15.34/2.52      | v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) != iProver_top
% 15.34/2.52      | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
% 15.34/2.52      | l1_pre_topc(X0) != iProver_top ),
% 15.34/2.52      inference(superposition,[status(thm)],[c_12657,c_3955]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_48535,plain,
% 15.34/2.52      ( v2_compts_1(sK1,X0) = iProver_top
% 15.34/2.52      | v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) != iProver_top
% 15.34/2.52      | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
% 15.34/2.52      | l1_pre_topc(X0) != iProver_top ),
% 15.34/2.52      inference(light_normalisation,[status(thm)],[c_48388,c_12657]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_48574,plain,
% 15.34/2.52      ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) != iProver_top
% 15.34/2.52      | v2_compts_1(sK1,sK0) = iProver_top
% 15.34/2.52      | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) != iProver_top
% 15.34/2.52      | l1_pre_topc(sK0) != iProver_top ),
% 15.34/2.52      inference(instantiation,[status(thm)],[c_48535]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_59577,plain,
% 15.34/2.52      ( v2_compts_1(sK1,sK0) = iProver_top ),
% 15.34/2.52      inference(global_propositional_subsumption,
% 15.34/2.52                [status(thm)],
% 15.34/2.52                [c_58580,c_24,c_25,c_26,c_48,c_49,c_1013,c_1014,c_1053,
% 15.34/2.52                 c_1063,c_1120,c_1167,c_3084,c_3137,c_3138,c_3147,c_3165,
% 15.34/2.52                 c_4903,c_4904,c_5177,c_7755,c_9951,c_17645,c_27935,
% 15.34/2.52                 c_37528,c_39021,c_46773,c_48574]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_59579,plain,
% 15.34/2.52      ( v2_compts_1(sK1,sK0) ),
% 15.34/2.52      inference(predicate_to_equality_rev,[status(thm)],[c_59577]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_27966,plain,
% 15.34/2.52      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.34/2.52      inference(predicate_to_equality_rev,[status(thm)],[c_27935]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_3256,plain,
% 15.34/2.52      ( v2_compts_1(u1_struct_0(X0),X1) != iProver_top
% 15.34/2.52      | v2_compts_1(u1_struct_0(X0),X0) = iProver_top
% 15.34/2.52      | m1_pre_topc(X0,X1) != iProver_top
% 15.34/2.52      | l1_pre_topc(X1) != iProver_top ),
% 15.34/2.52      inference(superposition,[status(thm)],[c_1739,c_928]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_26293,plain,
% 15.34/2.52      ( v2_compts_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_pre_topc(sK0,sK1)) = iProver_top
% 15.34/2.52      | v2_compts_1(sK1,X0) != iProver_top
% 15.34/2.52      | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
% 15.34/2.52      | l1_pre_topc(X0) != iProver_top ),
% 15.34/2.52      inference(superposition,[status(thm)],[c_12657,c_3256]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_26342,plain,
% 15.34/2.52      ( v2_compts_1(sK1,X0) != iProver_top
% 15.34/2.52      | v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) = iProver_top
% 15.34/2.52      | m1_pre_topc(k1_pre_topc(sK0,sK1),X0) != iProver_top
% 15.34/2.52      | l1_pre_topc(X0) != iProver_top ),
% 15.34/2.52      inference(light_normalisation,[status(thm)],[c_26293,c_12657]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_26356,plain,
% 15.34/2.52      ( ~ v2_compts_1(sK1,X0)
% 15.34/2.52      | v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
% 15.34/2.52      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
% 15.34/2.52      | ~ l1_pre_topc(X0) ),
% 15.34/2.52      inference(predicate_to_equality_rev,[status(thm)],[c_26342]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_26358,plain,
% 15.34/2.52      ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
% 15.34/2.52      | ~ v2_compts_1(sK1,sK0)
% 15.34/2.52      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
% 15.34/2.52      | ~ l1_pre_topc(sK0) ),
% 15.34/2.52      inference(instantiation,[status(thm)],[c_26356]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(c_19,negated_conjecture,
% 15.34/2.52      ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 15.34/2.52      | ~ v2_compts_1(sK1,sK0)
% 15.34/2.52      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
% 15.34/2.52      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.34/2.52      inference(cnf_transformation,[],[f67]) ).
% 15.34/2.52  
% 15.34/2.52  cnf(contradiction,plain,
% 15.34/2.52      ( $false ),
% 15.34/2.52      inference(minisat,
% 15.34/2.52                [status(thm)],
% 15.34/2.52                [c_67742,c_59579,c_46773,c_39015,c_27966,c_26358,c_17644,
% 15.34/2.52                 c_12657,c_9951,c_5174,c_4903,c_3165,c_3147,c_3084,
% 15.34/2.52                 c_1167,c_1119,c_1052,c_1013,c_48,c_19,c_24]) ).
% 15.34/2.52  
% 15.34/2.52  
% 15.34/2.52  % SZS output end CNFRefutation for theBenchmark.p
% 15.34/2.52  
% 15.34/2.52  ------                               Statistics
% 15.34/2.52  
% 15.34/2.52  ------ General
% 15.34/2.52  
% 15.34/2.52  abstr_ref_over_cycles:                  0
% 15.34/2.52  abstr_ref_under_cycles:                 0
% 15.34/2.52  gc_basic_clause_elim:                   0
% 15.34/2.52  forced_gc_time:                         0
% 15.34/2.52  parsing_time:                           0.016
% 15.34/2.52  unif_index_cands_time:                  0.
% 15.34/2.52  unif_index_add_time:                    0.
% 15.34/2.52  orderings_time:                         0.
% 15.34/2.52  out_proof_time:                         0.02
% 15.34/2.52  total_time:                             1.949
% 15.34/2.52  num_of_symbols:                         46
% 15.34/2.52  num_of_terms:                           52227
% 15.34/2.52  
% 15.34/2.52  ------ Preprocessing
% 15.34/2.52  
% 15.34/2.52  num_of_splits:                          0
% 15.34/2.52  num_of_split_atoms:                     0
% 15.34/2.52  num_of_reused_defs:                     0
% 15.34/2.52  num_eq_ax_congr_red:                    10
% 15.34/2.52  num_of_sem_filtered_clauses:            1
% 15.34/2.52  num_of_subtypes:                        0
% 15.34/2.52  monotx_restored_types:                  0
% 15.34/2.52  sat_num_of_epr_types:                   0
% 15.34/2.52  sat_num_of_non_cyclic_types:            0
% 15.34/2.52  sat_guarded_non_collapsed_types:        0
% 15.34/2.52  num_pure_diseq_elim:                    0
% 15.34/2.52  simp_replaced_by:                       0
% 15.34/2.52  res_preprocessed:                       100
% 15.34/2.52  prep_upred:                             0
% 15.34/2.52  prep_unflattend:                        2
% 15.34/2.52  smt_new_axioms:                         0
% 15.34/2.52  pred_elim_cands:                        5
% 15.34/2.52  pred_elim:                              0
% 15.34/2.52  pred_elim_cl:                           0
% 15.34/2.52  pred_elim_cycles:                       1
% 15.34/2.52  merged_defs:                            0
% 15.34/2.52  merged_defs_ncl:                        0
% 15.34/2.52  bin_hyper_res:                          0
% 15.34/2.52  prep_cycles:                            3
% 15.34/2.52  pred_elim_time:                         0.001
% 15.34/2.52  splitting_time:                         0.
% 15.34/2.52  sem_filter_time:                        0.
% 15.34/2.52  monotx_time:                            0.
% 15.34/2.52  subtype_inf_time:                       0.
% 15.34/2.52  
% 15.34/2.52  ------ Problem properties
% 15.34/2.52  
% 15.34/2.52  clauses:                                25
% 15.34/2.52  conjectures:                            6
% 15.34/2.52  epr:                                    2
% 15.34/2.52  horn:                                   20
% 15.34/2.52  ground:                                 6
% 15.34/2.52  unary:                                  2
% 15.34/2.52  binary:                                 9
% 15.34/2.52  lits:                                   71
% 15.34/2.52  lits_eq:                                9
% 15.34/2.52  fd_pure:                                0
% 15.34/2.52  fd_pseudo:                              0
% 15.34/2.52  fd_cond:                                1
% 15.34/2.52  fd_pseudo_cond:                         2
% 15.34/2.52  ac_symbols:                             0
% 15.34/2.52  
% 15.34/2.52  ------ Propositional Solver
% 15.34/2.52  
% 15.34/2.52  prop_solver_calls:                      28
% 15.34/2.52  prop_fast_solver_calls:                 2314
% 15.34/2.52  smt_solver_calls:                       0
% 15.34/2.52  smt_fast_solver_calls:                  0
% 15.34/2.52  prop_num_of_clauses:                    22607
% 15.34/2.52  prop_preprocess_simplified:             34359
% 15.34/2.52  prop_fo_subsumed:                       216
% 15.34/2.52  prop_solver_time:                       0.
% 15.34/2.52  smt_solver_time:                        0.
% 15.34/2.52  smt_fast_solver_time:                   0.
% 15.34/2.52  prop_fast_solver_time:                  0.
% 15.34/2.52  prop_unsat_core_time:                   0.002
% 15.34/2.52  
% 15.34/2.52  ------ QBF
% 15.34/2.52  
% 15.34/2.52  qbf_q_res:                              0
% 15.34/2.52  qbf_num_tautologies:                    0
% 15.34/2.52  qbf_prep_cycles:                        0
% 15.34/2.52  
% 15.34/2.52  ------ BMC1
% 15.34/2.52  
% 15.34/2.52  bmc1_current_bound:                     -1
% 15.34/2.52  bmc1_last_solved_bound:                 -1
% 15.34/2.52  bmc1_unsat_core_size:                   -1
% 15.34/2.52  bmc1_unsat_core_parents_size:           -1
% 15.34/2.52  bmc1_merge_next_fun:                    0
% 15.34/2.52  bmc1_unsat_core_clauses_time:           0.
% 15.34/2.52  
% 15.34/2.52  ------ Instantiation
% 15.34/2.52  
% 15.34/2.52  inst_num_of_clauses:                    5177
% 15.34/2.52  inst_num_in_passive:                    3413
% 15.34/2.52  inst_num_in_active:                     1763
% 15.34/2.52  inst_num_in_unprocessed:                0
% 15.34/2.52  inst_num_of_loops:                      2254
% 15.34/2.52  inst_num_of_learning_restarts:          0
% 15.34/2.52  inst_num_moves_active_passive:          486
% 15.34/2.52  inst_lit_activity:                      0
% 15.34/2.52  inst_lit_activity_moves:                1
% 15.34/2.52  inst_num_tautologies:                   0
% 15.34/2.52  inst_num_prop_implied:                  0
% 15.34/2.52  inst_num_existing_simplified:           0
% 15.34/2.52  inst_num_eq_res_simplified:             0
% 15.34/2.52  inst_num_child_elim:                    0
% 15.34/2.52  inst_num_of_dismatching_blockings:      7638
% 15.34/2.52  inst_num_of_non_proper_insts:           7837
% 15.34/2.52  inst_num_of_duplicates:                 0
% 15.34/2.52  inst_inst_num_from_inst_to_res:         0
% 15.34/2.52  inst_dismatching_checking_time:         0.
% 15.34/2.52  
% 15.34/2.52  ------ Resolution
% 15.34/2.52  
% 15.34/2.52  res_num_of_clauses:                     0
% 15.34/2.52  res_num_in_passive:                     0
% 15.34/2.52  res_num_in_active:                      0
% 15.34/2.52  res_num_of_loops:                       103
% 15.34/2.52  res_forward_subset_subsumed:            817
% 15.34/2.52  res_backward_subset_subsumed:           6
% 15.34/2.52  res_forward_subsumed:                   0
% 15.34/2.52  res_backward_subsumed:                  0
% 15.34/2.52  res_forward_subsumption_resolution:     0
% 15.34/2.52  res_backward_subsumption_resolution:    0
% 15.34/2.52  res_clause_to_clause_subsumption:       8019
% 15.34/2.52  res_orphan_elimination:                 0
% 15.34/2.52  res_tautology_del:                      408
% 15.34/2.52  res_num_eq_res_simplified:              0
% 15.34/2.52  res_num_sel_changes:                    0
% 15.34/2.52  res_moves_from_active_to_pass:          0
% 15.34/2.52  
% 15.34/2.52  ------ Superposition
% 15.34/2.52  
% 15.34/2.52  sup_time_total:                         0.
% 15.34/2.52  sup_time_generating:                    0.
% 15.34/2.52  sup_time_sim_full:                      0.
% 15.34/2.52  sup_time_sim_immed:                     0.
% 15.34/2.52  
% 15.34/2.52  sup_num_of_clauses:                     2399
% 15.34/2.52  sup_num_in_active:                      368
% 15.34/2.52  sup_num_in_passive:                     2031
% 15.34/2.52  sup_num_of_loops:                       450
% 15.34/2.52  sup_fw_superposition:                   1127
% 15.34/2.52  sup_bw_superposition:                   2285
% 15.34/2.52  sup_immediate_simplified:               1049
% 15.34/2.52  sup_given_eliminated:                   2
% 15.34/2.52  comparisons_done:                       0
% 15.34/2.52  comparisons_avoided:                    29
% 15.34/2.52  
% 15.34/2.52  ------ Simplifications
% 15.34/2.52  
% 15.34/2.52  
% 15.34/2.52  sim_fw_subset_subsumed:                 207
% 15.34/2.52  sim_bw_subset_subsumed:                 207
% 15.34/2.52  sim_fw_subsumed:                        311
% 15.34/2.52  sim_bw_subsumed:                        42
% 15.34/2.52  sim_fw_subsumption_res:                 5
% 15.34/2.52  sim_bw_subsumption_res:                 23
% 15.34/2.52  sim_tautology_del:                      73
% 15.34/2.52  sim_eq_tautology_del:                   44
% 15.34/2.52  sim_eq_res_simp:                        0
% 15.34/2.52  sim_fw_demodulated:                     28
% 15.34/2.52  sim_bw_demodulated:                     52
% 15.34/2.52  sim_light_normalised:                   554
% 15.34/2.52  sim_joinable_taut:                      0
% 15.34/2.52  sim_joinable_simp:                      0
% 15.34/2.52  sim_ac_normalised:                      0
% 15.34/2.52  sim_smt_subsumption:                    0
% 15.34/2.52  
%------------------------------------------------------------------------------
