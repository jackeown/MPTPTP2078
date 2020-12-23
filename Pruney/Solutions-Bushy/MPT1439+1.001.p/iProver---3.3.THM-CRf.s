%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1439+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:41 EST 2020

% Result     : Theorem 0.72s
% Output     : CNFRefutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 189 expanded)
%              Number of clauses        :   27 (  32 expanded)
%              Number of leaves         :    7 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  310 (1920 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X0,X1) )
               => r4_wellord1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X2)
      | ~ r4_wellord1(X1,X2)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => v1_relat_1(k8_filter_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( v1_relat_1(k8_filter_1(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( v1_relat_1(k8_filter_1(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(k8_filter_1(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l3_lattices(X2)
                & v10_lattices(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r1_filter_1(X1,X2)
                  & r1_filter_1(X0,X1) )
               => r1_filter_1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l3_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l3_lattices(X2)
                  & v10_lattices(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r1_filter_1(X1,X2)
                    & r1_filter_1(X0,X1) )
                 => r1_filter_1(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_filter_1(X0,X2)
              & r1_filter_1(X1,X2)
              & r1_filter_1(X0,X1)
              & l3_lattices(X2)
              & v10_lattices(X2)
              & ~ v2_struct_0(X2) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_filter_1(X0,X2)
              & r1_filter_1(X1,X2)
              & r1_filter_1(X0,X1)
              & l3_lattices(X2)
              & v10_lattices(X2)
              & ~ v2_struct_0(X2) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_filter_1(X0,X2)
          & r1_filter_1(X1,X2)
          & r1_filter_1(X0,X1)
          & l3_lattices(X2)
          & v10_lattices(X2)
          & ~ v2_struct_0(X2) )
     => ( ~ r1_filter_1(X0,sK2)
        & r1_filter_1(X1,sK2)
        & r1_filter_1(X0,X1)
        & l3_lattices(sK2)
        & v10_lattices(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_filter_1(X0,X2)
              & r1_filter_1(X1,X2)
              & r1_filter_1(X0,X1)
              & l3_lattices(X2)
              & v10_lattices(X2)
              & ~ v2_struct_0(X2) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r1_filter_1(X0,X2)
            & r1_filter_1(sK1,X2)
            & r1_filter_1(X0,sK1)
            & l3_lattices(X2)
            & v10_lattices(X2)
            & ~ v2_struct_0(X2) )
        & l3_lattices(sK1)
        & v10_lattices(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_filter_1(X0,X2)
                & r1_filter_1(X1,X2)
                & r1_filter_1(X0,X1)
                & l3_lattices(X2)
                & v10_lattices(X2)
                & ~ v2_struct_0(X2) )
            & l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_filter_1(sK0,X2)
              & r1_filter_1(X1,X2)
              & r1_filter_1(sK0,X1)
              & l3_lattices(X2)
              & v10_lattices(X2)
              & ~ v2_struct_0(X2) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ~ r1_filter_1(sK0,sK2)
    & r1_filter_1(sK1,sK2)
    & r1_filter_1(sK0,sK1)
    & l3_lattices(sK2)
    & v10_lattices(sK2)
    & ~ v2_struct_0(sK2)
    & l3_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1)
    & l3_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f17,f16,f15])).

fof(f28,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( r1_filter_1(X0,X1)
          <=> r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_filter_1(X0,X1)
          <=> r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_filter_1(X0,X1)
          <=> r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_filter_1(X0,X1)
              | ~ r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) )
            & ( r4_wellord1(k8_filter_1(X0),k8_filter_1(X1))
              | ~ r1_filter_1(X0,X1) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r4_wellord1(k8_filter_1(X0),k8_filter_1(X1))
      | ~ r1_filter_1(X0,X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    r1_filter_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    r1_filter_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_filter_1(X0,X1)
      | ~ r4_wellord1(k8_filter_1(X0),k8_filter_1(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ~ r1_filter_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f25,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_3,plain,
    ( ~ r4_wellord1(X0,X1)
    | ~ r4_wellord1(X2,X0)
    | r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_271,plain,
    ( ~ r4_wellord1(X0_38,X1_38)
    | ~ r4_wellord1(X2_38,X0_38)
    | r4_wellord1(X2_38,X1_38)
    | ~ v1_relat_1(X1_38)
    | ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(X2_38) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_303,plain,
    ( ~ r4_wellord1(X0_38,X1_38)
    | ~ r4_wellord1(X1_38,k8_filter_1(sK2))
    | r4_wellord1(X0_38,k8_filter_1(sK2))
    | ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(X1_38)
    | ~ v1_relat_1(k8_filter_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_309,plain,
    ( ~ r4_wellord1(X0_38,k8_filter_1(sK2))
    | ~ r4_wellord1(k8_filter_1(sK0),X0_38)
    | r4_wellord1(k8_filter_1(sK0),k8_filter_1(sK2))
    | ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(k8_filter_1(sK2))
    | ~ v1_relat_1(k8_filter_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_316,plain,
    ( ~ r4_wellord1(k8_filter_1(sK1),k8_filter_1(sK2))
    | ~ r4_wellord1(k8_filter_1(sK0),k8_filter_1(sK1))
    | r4_wellord1(k8_filter_1(sK0),k8_filter_1(sK2))
    | ~ v1_relat_1(k8_filter_1(sK1))
    | ~ v1_relat_1(k8_filter_1(sK2))
    | ~ v1_relat_1(k8_filter_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_2,plain,
    ( v1_relat_1(k8_filter_1(X0))
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_10,negated_conjecture,
    ( l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_197,plain,
    ( v1_relat_1(k8_filter_1(sK1))
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1) ),
    inference(resolution,[status(thm)],[c_2,c_10])).

cnf(c_7,negated_conjecture,
    ( l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_187,plain,
    ( v1_relat_1(k8_filter_1(sK2))
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK2) ),
    inference(resolution,[status(thm)],[c_2,c_7])).

cnf(c_1,plain,
    ( r4_wellord1(k8_filter_1(X0),k8_filter_1(X1))
    | ~ r1_filter_1(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_6,negated_conjecture,
    ( r1_filter_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_171,plain,
    ( r4_wellord1(k8_filter_1(sK0),k8_filter_1(sK1))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK1)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK1)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[status(thm)],[c_1,c_6])).

cnf(c_5,negated_conjecture,
    ( r1_filter_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_161,plain,
    ( r4_wellord1(k8_filter_1(sK1),k8_filter_1(sK2))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v10_lattices(sK1)
    | ~ v10_lattices(sK2)
    | ~ l3_lattices(sK1)
    | ~ l3_lattices(sK2) ),
    inference(resolution,[status(thm)],[c_1,c_5])).

cnf(c_0,plain,
    ( ~ r4_wellord1(k8_filter_1(X0),k8_filter_1(X1))
    | r1_filter_1(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_4,negated_conjecture,
    ( ~ r1_filter_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_151,plain,
    ( ~ r4_wellord1(k8_filter_1(sK0),k8_filter_1(sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK2)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK2)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[status(thm)],[c_0,c_4])).

cnf(c_30,plain,
    ( v1_relat_1(k8_filter_1(sK0))
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_8,negated_conjecture,
    ( v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_9,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_11,negated_conjecture,
    ( v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_12,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_13,negated_conjecture,
    ( l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_14,negated_conjecture,
    ( v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_15,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_316,c_197,c_187,c_171,c_161,c_151,c_30,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15])).


%------------------------------------------------------------------------------
