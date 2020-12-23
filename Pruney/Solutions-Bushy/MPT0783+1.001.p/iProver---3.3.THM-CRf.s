%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0783+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:07 EST 2020

% Result     : Theorem 0.67s
% Output     : CNFRefutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 108 expanded)
%              Number of clauses        :   34 (  34 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  250 ( 492 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
       => v1_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
       => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( v4_relat_2(k2_wellord1(X1,X0))
      | ~ v4_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v4_relat_2(k2_wellord1(X1,X0))
      | ~ v4_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v4_relat_2(k2_wellord1(X1,X0))
      | ~ v4_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
       => v8_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( v8_relat_2(k2_wellord1(X1,X0))
      | ~ v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v8_relat_2(k2_wellord1(X1,X0))
      | ~ v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v8_relat_2(k2_wellord1(X1,X0))
      | ~ v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
       => v6_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( v6_relat_2(k2_wellord1(X1,X0))
      | ~ v6_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v6_relat_2(k2_wellord1(X1,X0))
      | ~ v6_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v6_relat_2(k2_wellord1(X1,X0))
      | ~ v6_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
       => v1_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f33,plain,(
    ! [X0] :
      ( v2_wellord1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ~ v2_wellord1(k2_wellord1(X1,X0))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ~ v2_wellord1(k2_wellord1(X1,X0))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ~ v2_wellord1(k2_wellord1(X1,X0))
        & v2_wellord1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_wellord1(k2_wellord1(sK1,sK0))
      & v2_wellord1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ v2_wellord1(k2_wellord1(sK1,sK0))
    & v2_wellord1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).

fof(f42,plain,(
    ~ v2_wellord1(k2_wellord1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f32,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f30,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f29,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_wellord1(X0)
    | v1_wellord1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_337,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v1_wellord1(X0_38)
    | v1_wellord1(k2_wellord1(X0_38,X0_39)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_359,plain,
    ( ~ v1_relat_1(sK1)
    | v1_wellord1(k2_wellord1(sK1,sK0))
    | ~ v1_wellord1(sK1) ),
    inference(instantiation,[status(thm)],[c_337])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v4_relat_2(X0)
    | v4_relat_2(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_338,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v4_relat_2(X0_38)
    | v4_relat_2(k2_wellord1(X0_38,X0_39)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_356,plain,
    ( ~ v1_relat_1(sK1)
    | v4_relat_2(k2_wellord1(sK1,sK0))
    | ~ v4_relat_2(sK1) ),
    inference(instantiation,[status(thm)],[c_338])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v8_relat_2(X0)
    | v8_relat_2(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_339,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v8_relat_2(X0_38)
    | v8_relat_2(k2_wellord1(X0_38,X0_39)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_353,plain,
    ( ~ v1_relat_1(sK1)
    | v8_relat_2(k2_wellord1(sK1,sK0))
    | ~ v8_relat_2(sK1) ),
    inference(instantiation,[status(thm)],[c_339])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v6_relat_2(X0)
    | v6_relat_2(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_340,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v6_relat_2(X0_38)
    | v6_relat_2(k2_wellord1(X0_38,X0_39)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_350,plain,
    ( ~ v1_relat_1(sK1)
    | v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ v6_relat_2(sK1) ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_2(X0)
    | v1_relat_2(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_341,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v1_relat_2(X0_38)
    | v1_relat_2(k2_wellord1(X0_38,X0_39)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_347,plain,
    ( ~ v1_relat_1(sK1)
    | v1_relat_2(k2_wellord1(sK1,sK0))
    | ~ v1_relat_2(sK1) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_342,plain,
    ( ~ v1_relat_1(X0_38)
    | v1_relat_1(k2_wellord1(X0_38,X0_39)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_344,plain,
    ( v1_relat_1(k2_wellord1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_2(X0)
    | ~ v8_relat_2(X0)
    | ~ v4_relat_2(X0)
    | ~ v6_relat_2(X0)
    | ~ v1_wellord1(X0)
    | v2_wellord1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_12,negated_conjecture,
    ( ~ v2_wellord1(k2_wellord1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_163,plain,
    ( ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | ~ v1_relat_2(k2_wellord1(sK1,sK0))
    | ~ v8_relat_2(k2_wellord1(sK1,sK0))
    | ~ v4_relat_2(k2_wellord1(sK1,sK0))
    | ~ v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ v1_wellord1(k2_wellord1(sK1,sK0)) ),
    inference(resolution,[status(thm)],[c_0,c_12])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_wellord1(X0)
    | ~ v2_wellord1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_49,plain,
    ( ~ v1_relat_1(sK1)
    | v1_wellord1(sK1)
    | ~ v2_wellord1(sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v6_relat_2(X0)
    | ~ v2_wellord1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_46,plain,
    ( ~ v1_relat_1(sK1)
    | v6_relat_2(sK1)
    | ~ v2_wellord1(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | v4_relat_2(X0)
    | ~ v2_wellord1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_43,plain,
    ( ~ v1_relat_1(sK1)
    | v4_relat_2(sK1)
    | ~ v2_wellord1(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v8_relat_2(X0)
    | ~ v2_wellord1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_40,plain,
    ( ~ v1_relat_1(sK1)
    | v8_relat_2(sK1)
    | ~ v2_wellord1(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_2(X0)
    | ~ v2_wellord1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_37,plain,
    ( ~ v1_relat_1(sK1)
    | v1_relat_2(sK1)
    | ~ v2_wellord1(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_13,negated_conjecture,
    ( v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_359,c_356,c_353,c_350,c_347,c_344,c_163,c_49,c_46,c_43,c_40,c_37,c_13,c_14])).


%------------------------------------------------------------------------------
