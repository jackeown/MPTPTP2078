%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1589+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:58 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 172 expanded)
%              Number of clauses        :   31 (  33 expanded)
%              Number of leaves         :    6 (  54 expanded)
%              Depth                    :   21
%              Number of atoms          :  295 (1595 expanded)
%              Number of equality atoms :   43 ( 187 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
               => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                 => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                 => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
              & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
              & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
          & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k2_yellow_0(X0,sK2) != k2_yellow_0(X1,sK2)
        & r2_hidden(k2_yellow_0(X0,sK2),u1_struct_0(X1))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
              & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( k2_yellow_0(sK1,X2) != k2_yellow_0(X0,X2)
            & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(sK1))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_yellow_0(sK1,X0)
        & v4_yellow_0(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                & r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(sK0,X2) != k2_yellow_0(X1,X2)
              & r2_hidden(k2_yellow_0(sK0,X2),u1_struct_0(X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,sK0)
          & v4_yellow_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & v3_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)
    & r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_yellow_0(sK1,sK0)
    & v4_yellow_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & v3_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15,f14,f13])).

fof(f30,plain,(
    k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                  & r2_yellow_0(X0,X2) )
               => ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                  & r2_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
      | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f21,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : r2_yellow_0(X0,X1) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] : r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] : r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f23,plain,(
    v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f22,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_3,negated_conjecture,
    ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_345,negated_conjecture,
    ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_6,negated_conjecture,
    ( m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_5,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( ~ v4_yellow_0(X0,X1)
    | ~ m1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(k2_yellow_0(X1,X2),u1_struct_0(X0))
    | ~ r2_yellow_0(X1,X2)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X1)
    | k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_9,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_183,plain,
    ( ~ v4_yellow_0(X0,X1)
    | ~ m1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(k2_yellow_0(X1,X2),u1_struct_0(X0))
    | ~ r2_yellow_0(X1,X2)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k2_yellow_0(X1,X2) = k2_yellow_0(X0,X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_184,plain,
    ( ~ v4_yellow_0(X0,sK0)
    | ~ m1_yellow_0(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(k2_yellow_0(sK0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(sK0,X1)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | k2_yellow_0(sK0,X1) = k2_yellow_0(X0,X1) ),
    inference(unflattening,[status(thm)],[c_183])).

cnf(c_13,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_12,negated_conjecture,
    ( v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_188,plain,
    ( v2_struct_0(X0)
    | ~ v4_yellow_0(X0,sK0)
    | ~ m1_yellow_0(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(k2_yellow_0(sK0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(sK0,X1)
    | k2_yellow_0(sK0,X1) = k2_yellow_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_184,c_13,c_12])).

cnf(c_189,plain,
    ( ~ v4_yellow_0(X0,sK0)
    | ~ m1_yellow_0(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(k2_yellow_0(sK0,X1),u1_struct_0(X0))
    | ~ r2_yellow_0(sK0,X1)
    | v2_struct_0(X0)
    | k2_yellow_0(sK0,X1) = k2_yellow_0(X0,X1) ),
    inference(renaming,[status(thm)],[c_188])).

cnf(c_0,plain,
    ( r2_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_10,negated_conjecture,
    ( v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_137,plain,
    ( r2_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_138,plain,
    ( r2_yellow_0(sK0,X0)
    | v2_struct_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_137])).

cnf(c_11,negated_conjecture,
    ( v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_142,plain,
    ( r2_yellow_0(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_138,c_13,c_11,c_9])).

cnf(c_208,plain,
    ( ~ v4_yellow_0(X0,sK0)
    | ~ m1_yellow_0(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(k2_yellow_0(sK0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | k2_yellow_0(sK0,X1) = k2_yellow_0(X0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_189,c_142])).

cnf(c_265,plain,
    ( ~ v4_yellow_0(X0,sK0)
    | ~ m1_yellow_0(X0,sK0)
    | ~ r2_hidden(k2_yellow_0(sK0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | k2_yellow_0(X0,X1) = k2_yellow_0(sK0,X1)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_208])).

cnf(c_266,plain,
    ( ~ v4_yellow_0(X0,sK0)
    | ~ m1_yellow_0(X0,sK0)
    | ~ r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | k2_yellow_0(X0,sK2) = k2_yellow_0(sK0,sK2)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_327,plain,
    ( ~ v4_yellow_0(X0,sK0)
    | ~ r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | k2_yellow_0(X0,sK2) = k2_yellow_0(sK0,sK2)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_266])).

cnf(c_328,plain,
    ( ~ v4_yellow_0(sK1,sK0)
    | ~ r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | k2_yellow_0(sK1,sK2) = k2_yellow_0(sK0,sK2)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_8,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_7,negated_conjecture,
    ( v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_4,negated_conjecture,
    ( r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_330,plain,
    ( k2_yellow_0(sK1,sK2) = k2_yellow_0(sK0,sK2)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_8,c_7,c_4])).

cnf(c_340,plain,
    ( k2_yellow_0(sK1,sK2) = k2_yellow_0(sK0,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_330])).

cnf(c_344,plain,
    ( k2_yellow_0(sK1,sK2) = k2_yellow_0(sK0,sK2) ),
    inference(subtyping,[status(esa)],[c_340])).

cnf(c_349,plain,
    ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_345,c_344])).

cnf(c_350,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_349])).


%------------------------------------------------------------------------------
