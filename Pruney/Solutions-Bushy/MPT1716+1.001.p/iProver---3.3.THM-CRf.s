%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1716+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:15 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   50 (  94 expanded)
%              Number of clauses        :   26 (  27 expanded)
%              Number of leaves         :    8 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  199 ( 489 expanded)
%              Number of equality atoms :   37 (  91 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X2)
                  | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tsep_1(X0,X1,X1) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tsep_1(X0,X1,X1) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_tsep_1(X0,X1,X1) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( k1_tsep_1(X0,sK1,sK1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_tsep_1(X0,X1,X1) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_tsep_1(sK0,X1,X1) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( k1_tsep_1(sK0,sK1,sK1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14,f13])).

fof(f21,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,(
    k1_tsep_1(sK0,sK1,sK1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f23,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_240,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_411,plain,
    ( k1_tsep_1(sK0,sK1,sK1) = k1_tsep_1(sK0,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_241,plain,
    ( X0_39 != X1_39
    | X2_39 != X1_39
    | X2_39 = X0_39 ),
    theory(equality)).

cnf(c_404,plain,
    ( k1_tsep_1(sK0,sK1,sK1) != X0_39
    | k1_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != X0_39 ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_410,plain,
    ( k1_tsep_1(sK0,sK1,sK1) != k1_tsep_1(sK0,sK1,sK1)
    | k1_tsep_1(sK0,sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k1_tsep_1(sK0,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_239,plain,
    ( ~ m1_pre_topc(X0_38,X1_38)
    | ~ l1_pre_topc(X1_38)
    | l1_pre_topc(X0_38) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_394,plain,
    ( ~ m1_pre_topc(X0_38,sK0)
    | l1_pre_topc(X0_38)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_396,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_8,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_98,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X0,X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_99,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X0,X1) ),
    inference(unflattening,[status(thm)],[c_98])).

cnf(c_9,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_7,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_103,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_99,c_9,c_7])).

cnf(c_104,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(sK0,X0,X1) ),
    inference(renaming,[status(thm)],[c_103])).

cnf(c_232,plain,
    ( ~ m1_pre_topc(X0_38,X1_38)
    | ~ m1_pre_topc(X0_38,sK0)
    | ~ m1_pre_topc(X1_38,sK0)
    | v2_struct_0(X1_38)
    | v2_struct_0(X0_38)
    | g1_pre_topc(u1_struct_0(X1_38),u1_pre_topc(X1_38)) = k1_tsep_1(sK0,X0_38,X1_38) ),
    inference(subtyping,[status(esa)],[c_104])).

cnf(c_250,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_4,negated_conjecture,
    ( k1_tsep_1(sK0,sK1,sK1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_237,negated_conjecture,
    ( k1_tsep_1(sK0,sK1,sK1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_16,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_6,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_411,c_410,c_396,c_250,c_237,c_16,c_5,c_6,c_7])).


%------------------------------------------------------------------------------
