%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1579+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:56 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 119 expanded)
%              Number of clauses        :   24 (  30 expanded)
%              Number of leaves         :    5 (  38 expanded)
%              Depth                    :   16
%              Number of atoms          :  134 ( 720 expanded)
%              Number of equality atoms :   52 ( 240 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
         => ! [X2] :
              ( ( m1_yellow_0(X2,X0)
                & v4_yellow_0(X2,X0) )
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0) )
           => ! [X2] :
                ( ( m1_yellow_0(X2,X0)
                  & v4_yellow_0(X2,X0) )
               => ( u1_struct_0(X1) = u1_struct_0(X2)
                 => g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_yellow_0(X2,X0)
              & v4_yellow_0(X2,X0) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_yellow_0(X2,X0)
              & v4_yellow_0(X2,X0) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f5])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
          & u1_struct_0(X1) = u1_struct_0(X2)
          & m1_yellow_0(X2,X0)
          & v4_yellow_0(X2,X0) )
     => ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
        & u1_struct_0(sK2) = u1_struct_0(X1)
        & m1_yellow_0(sK2,X0)
        & v4_yellow_0(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_yellow_0(X2,X0)
              & v4_yellow_0(X2,X0) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0) )
     => ( ? [X2] :
            ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
            & u1_struct_0(sK1) = u1_struct_0(X2)
            & m1_yellow_0(X2,X0)
            & v4_yellow_0(X2,X0) )
        & m1_yellow_0(sK1,X0)
        & v4_yellow_0(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                & u1_struct_0(X1) = u1_struct_0(X2)
                & m1_yellow_0(X2,X0)
                & v4_yellow_0(X2,X0) )
            & m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & m1_yellow_0(X2,sK0)
              & v4_yellow_0(X2,sK0) )
          & m1_yellow_0(X1,sK0)
          & v4_yellow_0(X1,sK0) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    & u1_struct_0(sK1) = u1_struct_0(sK2)
    & m1_yellow_0(sK2,sK0)
    & v4_yellow_0(sK2,sK0)
    & m1_yellow_0(sK1,sK0)
    & v4_yellow_0(sK1,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f10,f9,f8])).

fof(f20,plain,(
    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_yellow_0(X1,X0)
              | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
            & ( u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
              | ~ v4_yellow_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1] :
      ( u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f16,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f17,plain,(
    v4_yellow_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,plain,(
    m1_yellow_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_2,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_145,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3,negated_conjecture,
    ( u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_144,negated_conjecture,
    ( u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_7,negated_conjecture,
    ( v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_1,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ v4_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)) = u1_orders_2(X0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_8,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_79,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ v4_yellow_0(X0,X1)
    | k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)) = u1_orders_2(X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_80,plain,
    ( ~ m1_yellow_0(X0,sK0)
    | ~ v4_yellow_0(X0,sK0)
    | k1_toler_1(u1_orders_2(sK0),u1_struct_0(X0)) = u1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_79])).

cnf(c_126,plain,
    ( ~ m1_yellow_0(X0,sK0)
    | k1_toler_1(u1_orders_2(sK0),u1_struct_0(X0)) = u1_orders_2(X0)
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_80])).

cnf(c_127,plain,
    ( ~ m1_yellow_0(sK1,sK0)
    | k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1)) = u1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_126])).

cnf(c_6,negated_conjecture,
    ( m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_129,plain,
    ( k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1)) = u1_orders_2(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_127,c_6])).

cnf(c_142,plain,
    ( k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1)) = u1_orders_2(sK1) ),
    inference(subtyping,[status(esa)],[c_129])).

cnf(c_5,negated_conjecture,
    ( v4_yellow_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_118,plain,
    ( ~ m1_yellow_0(X0,sK0)
    | k1_toler_1(u1_orders_2(sK0),u1_struct_0(X0)) = u1_orders_2(X0)
    | sK0 != sK0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_80])).

cnf(c_119,plain,
    ( ~ m1_yellow_0(sK2,sK0)
    | k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK2)) = u1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_118])).

cnf(c_4,negated_conjecture,
    ( m1_yellow_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_121,plain,
    ( k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK2)) = u1_orders_2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_119,c_4])).

cnf(c_143,plain,
    ( k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK2)) = u1_orders_2(sK2) ),
    inference(subtyping,[status(esa)],[c_121])).

cnf(c_159,plain,
    ( k1_toler_1(u1_orders_2(sK0),u1_struct_0(sK1)) = u1_orders_2(sK2) ),
    inference(light_normalisation,[status(thm)],[c_143,c_144])).

cnf(c_160,plain,
    ( u1_orders_2(sK2) = u1_orders_2(sK1) ),
    inference(demodulation,[status(thm)],[c_142,c_159])).

cnf(c_161,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(light_normalisation,[status(thm)],[c_145,c_144,c_160])).

cnf(c_162,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_161])).


%------------------------------------------------------------------------------
