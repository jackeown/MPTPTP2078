%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1135+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:58 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 544 expanded)
%              Number of clauses        :   78 ( 192 expanded)
%              Number of leaves         :   11 ( 135 expanded)
%              Depth                    :   16
%              Number of atoms          :  367 (2153 expanded)
%              Number of equality atoms :  153 ( 819 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
             => ( X1 = X2
               => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
               => ( X1 = X2
                 => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
          & X1 = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
     => ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2)
        & sK2 = X1
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,sK1)),u1_pre_topc(k1_pre_topc(X0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
            & sK1 = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
                & X1 = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,X1)),u1_pre_topc(k1_pre_topc(sK0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK2)
    & sK1 = sK2
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f26,f25,f24])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    sK1 = sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
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

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

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
    inference(flattening,[],[f12])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_pre_topc(X0,X1) = X2
      | k2_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X2,X0] :
      ( k1_pre_topc(X0,k2_struct_0(X2)) = X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_633,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_952,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_12,negated_conjecture,
    ( sK1 = sK2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_634,negated_conjecture,
    ( sK1 = sK2 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_963,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_952,c_634])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(k1_pre_topc(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(k1_pre_topc(X1,X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_94,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_6,c_5])).

cnf(c_95,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_94])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_43)))
    | ~ l1_pre_topc(X0_43)
    | k2_struct_0(k1_pre_topc(X0_43,X0_41)) = X0_41 ),
    inference(subtyping,[status(esa)],[c_95])).

cnf(c_956,plain,
    ( k2_struct_0(k1_pre_topc(X0_43,X0_41)) = X0_41
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_2029,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_963,c_956])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_25,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_27,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_642,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(X0_42)))
    | l1_pre_topc(g1_pre_topc(X0_42,X0_41)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1075,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0_43),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_43))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))) ),
    inference(instantiation,[status(thm)],[c_642])).

cnf(c_1076,plain,
    ( m1_subset_1(u1_pre_topc(X0_43),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_43)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1075])).

cnf(c_1078,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1076])).

cnf(c_2121,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2029,c_16,c_27,c_1078])).

cnf(c_1,plain,
    ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X0)
    | k1_pre_topc(X1,k2_struct_0(X0)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_643,plain,
    ( ~ m1_subset_1(k2_struct_0(X0_43),k1_zfmisc_1(u1_struct_0(X1_43)))
    | ~ m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X1_43)
    | ~ v1_pre_topc(X0_43)
    | k1_pre_topc(X1_43,k2_struct_0(X0_43)) = X0_43 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_944,plain,
    ( k1_pre_topc(X0_43,k2_struct_0(X1_43)) = X1_43
    | m1_subset_1(k2_struct_0(X1_43),k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | v1_pre_topc(X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_2124,plain,
    ( k1_pre_topc(X0_43,k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0_43) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2121,c_944])).

cnf(c_2125,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(X0_43,sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0_43) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2124,c_2121])).

cnf(c_2127,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(sK0,sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2125])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_632,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_953,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_640,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_43)))
    | m1_pre_topc(k1_pre_topc(X0_43,X0_41),X0_43)
    | ~ l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_947,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
    | m1_pre_topc(k1_pre_topc(X0_43,X0_41),X0_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_1396,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_953,c_947])).

cnf(c_17,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_687,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
    | m1_pre_topc(k1_pre_topc(X0_43,X0_41),X0_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_689,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_687])).

cnf(c_1520,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1396,c_16,c_17,c_689])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_638,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X1_43)
    | l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_949,plain,
    ( m1_pre_topc(X0_43,X1_43) != iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | l1_pre_topc(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_1525,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1520,c_949])).

cnf(c_1335,plain,
    ( ~ m1_pre_topc(k1_pre_topc(X0_43,X0_41),X1_43)
    | ~ l1_pre_topc(X1_43)
    | l1_pre_topc(k1_pre_topc(X0_43,X0_41)) ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_1336,plain,
    ( m1_pre_topc(k1_pre_topc(X0_43,X0_41),X1_43) != iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | l1_pre_topc(k1_pre_topc(X0_43,X0_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1335])).

cnf(c_1338,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1336])).

cnf(c_1661,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1525,c_16,c_17,c_689,c_1338])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_644,plain,
    ( ~ l1_pre_topc(X0_43)
    | ~ v1_pre_topc(X0_43)
    | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = X0_43 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_943,plain,
    ( g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = X0_43
    | l1_pre_topc(X0_43) != iProver_top
    | v1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_1666,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(sK0,sK1)
    | v1_pre_topc(k1_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1661,c_943])).

cnf(c_688,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_640])).

cnf(c_639,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_43)))
    | ~ l1_pre_topc(X0_43)
    | v1_pre_topc(k1_pre_topc(X0_43,X0_41)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_691,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_1085,plain,
    ( ~ l1_pre_topc(k1_pre_topc(X0_43,X0_41))
    | ~ v1_pre_topc(k1_pre_topc(X0_43,X0_41))
    | g1_pre_topc(u1_struct_0(k1_pre_topc(X0_43,X0_41)),u1_pre_topc(k1_pre_topc(X0_43,X0_41))) = k1_pre_topc(X0_43,X0_41) ),
    inference(instantiation,[status(thm)],[c_644])).

cnf(c_1087,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
    | g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_1337,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1335])).

cnf(c_1932,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1666,c_15,c_14,c_688,c_691,c_1087,c_1337])).

cnf(c_11,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_635,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK2) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_984,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    inference(light_normalisation,[status(thm)],[c_635,c_634])).

cnf(c_1935,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != k1_pre_topc(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1932,c_984])).

cnf(c_1397,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_963,c_947])).

cnf(c_1122,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)))))
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X0_41),g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))) ),
    inference(instantiation,[status(thm)],[c_640])).

cnf(c_1127,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))))) != iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X0_41),g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1122])).

cnf(c_1129,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) != iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_1577,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1397,c_16,c_27,c_963,c_1078,c_1129])).

cnf(c_1582,plain,
    ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1577,c_949])).

cnf(c_948,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | v1_pre_topc(k1_pre_topc(X0_43,X0_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_1381,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_963,c_948])).

cnf(c_9,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_636,plain,
    ( m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43)))
    | ~ l1_pre_topc(X1_43)
    | ~ l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1121,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X0_41),X0_43)
    | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X0_41),g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)))
    | ~ l1_pre_topc(X0_43)
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X0_41)) ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(c_1123,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X0_41),X0_43) = iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X0_41),g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X0_41)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1121])).

cnf(c_1125,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) = iProver_top
    | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1123])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2127,c_1935,c_1582,c_1381,c_1129,c_1125,c_1078,c_963,c_27,c_17,c_16])).


%------------------------------------------------------------------------------
