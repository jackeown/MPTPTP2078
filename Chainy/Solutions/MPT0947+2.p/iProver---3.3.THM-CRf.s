%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0947+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:58 EST 2020

% Result     : Theorem 43.65s
% Output     : CNFRefutation 43.65s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 199 expanded)
%              Number of clauses        :   43 (  66 expanded)
%              Number of leaves         :    9 (  56 expanded)
%              Depth                    :   19
%              Number of atoms          :  234 ( 948 expanded)
%              Number of equality atoms :  106 ( 243 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1431,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r4_wellord1(X0,k1_wellord2(X2))
                  & r4_wellord1(X0,k1_wellord2(X1)) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1432,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ! [X2] :
                ( v3_ordinal1(X2)
               => ( ( r4_wellord1(X0,k1_wellord2(X2))
                    & r4_wellord1(X0,k1_wellord2(X1)) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f1431])).

fof(f2892,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r4_wellord1(X0,k1_wellord2(X2))
              & r4_wellord1(X0,k1_wellord2(X1))
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1432])).

fof(f2893,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r4_wellord1(X0,k1_wellord2(X2))
              & r4_wellord1(X0,k1_wellord2(X1))
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f2892])).

fof(f4032,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r4_wellord1(X0,k1_wellord2(X2))
          & r4_wellord1(X0,k1_wellord2(X1))
          & v3_ordinal1(X2) )
     => ( sK471 != X1
        & r4_wellord1(X0,k1_wellord2(sK471))
        & r4_wellord1(X0,k1_wellord2(X1))
        & v3_ordinal1(sK471) ) ) ),
    introduced(choice_axiom,[])).

fof(f4031,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r4_wellord1(X0,k1_wellord2(X2))
              & r4_wellord1(X0,k1_wellord2(X1))
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
     => ( ? [X2] :
            ( sK470 != X2
            & r4_wellord1(X0,k1_wellord2(X2))
            & r4_wellord1(X0,k1_wellord2(sK470))
            & v3_ordinal1(X2) )
        & v3_ordinal1(sK470) ) ) ),
    introduced(choice_axiom,[])).

fof(f4030,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & r4_wellord1(X0,k1_wellord2(X2))
                & r4_wellord1(X0,k1_wellord2(X1))
                & v3_ordinal1(X2) )
            & v3_ordinal1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r4_wellord1(sK469,k1_wellord2(X2))
              & r4_wellord1(sK469,k1_wellord2(X1))
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_relat_1(sK469) ) ),
    introduced(choice_axiom,[])).

fof(f4033,plain,
    ( sK470 != sK471
    & r4_wellord1(sK469,k1_wellord2(sK471))
    & r4_wellord1(sK469,k1_wellord2(sK470))
    & v3_ordinal1(sK471)
    & v3_ordinal1(sK470)
    & v1_relat_1(sK469) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK469,sK470,sK471])],[f2893,f4032,f4031,f4030])).

fof(f6625,plain,(
    r4_wellord1(sK469,k1_wellord2(sK471)) ),
    inference(cnf_transformation,[],[f4033])).

fof(f1192,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2644,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1192])).

fof(f2645,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2644])).

fof(f6093,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2645])).

fof(f6621,plain,(
    v1_relat_1(sK469) ),
    inference(cnf_transformation,[],[f4033])).

fof(f1423,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6610,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1423])).

fof(f1194,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X0,X1) )
               => r4_wellord1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2648,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1194])).

fof(f2649,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2648])).

fof(f6095,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X2)
      | ~ r4_wellord1(X1,X2)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2649])).

fof(f1430,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2890,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1430])).

fof(f2891,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f2890])).

fof(f6620,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f2891])).

fof(f6622,plain,(
    v3_ordinal1(sK470) ),
    inference(cnf_transformation,[],[f4033])).

fof(f6623,plain,(
    v3_ordinal1(sK471) ),
    inference(cnf_transformation,[],[f4033])).

fof(f6626,plain,(
    sK470 != sK471 ),
    inference(cnf_transformation,[],[f4033])).

fof(f6624,plain,(
    r4_wellord1(sK469,k1_wellord2(sK470)) ),
    inference(cnf_transformation,[],[f4033])).

cnf(c_2565,negated_conjecture,
    ( r4_wellord1(sK469,k1_wellord2(sK471)) ),
    inference(cnf_transformation,[],[f6625])).

cnf(c_73077,plain,
    ( r4_wellord1(sK469,k1_wellord2(sK471)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2565])).

cnf(c_2044,plain,
    ( ~ r4_wellord1(X0,X1)
    | r4_wellord1(X1,X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f6093])).

cnf(c_73524,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2044])).

cnf(c_143968,plain,
    ( r4_wellord1(k1_wellord2(sK471),sK469) = iProver_top
    | v1_relat_1(k1_wellord2(sK471)) != iProver_top
    | v1_relat_1(sK469) != iProver_top ),
    inference(superposition,[status(thm)],[c_73077,c_73524])).

cnf(c_2569,negated_conjecture,
    ( v1_relat_1(sK469) ),
    inference(cnf_transformation,[],[f6621])).

cnf(c_2578,plain,
    ( v1_relat_1(sK469) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2569])).

cnf(c_144600,plain,
    ( v1_relat_1(k1_wellord2(sK471)) != iProver_top
    | r4_wellord1(k1_wellord2(sK471),sK469) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_143968,c_2578])).

cnf(c_144601,plain,
    ( r4_wellord1(k1_wellord2(sK471),sK469) = iProver_top
    | v1_relat_1(k1_wellord2(sK471)) != iProver_top ),
    inference(renaming,[status(thm)],[c_144600])).

cnf(c_2553,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6610])).

cnf(c_73087,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2553])).

cnf(c_144606,plain,
    ( r4_wellord1(k1_wellord2(sK471),sK469) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_144601,c_73087])).

cnf(c_2046,plain,
    ( ~ r4_wellord1(X0,X1)
    | ~ r4_wellord1(X1,X2)
    | r4_wellord1(X0,X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f6095])).

cnf(c_73522,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | r4_wellord1(X1,X2) != iProver_top
    | r4_wellord1(X0,X2) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2046])).

cnf(c_144609,plain,
    ( r4_wellord1(k1_wellord2(sK471),X0) = iProver_top
    | r4_wellord1(sK469,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_wellord2(sK471)) != iProver_top
    | v1_relat_1(sK469) != iProver_top ),
    inference(superposition,[status(thm)],[c_144606,c_73522])).

cnf(c_147395,plain,
    ( v1_relat_1(k1_wellord2(sK471)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | r4_wellord1(sK469,X0) != iProver_top
    | r4_wellord1(k1_wellord2(sK471),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_144609,c_2578])).

cnf(c_147396,plain,
    ( r4_wellord1(k1_wellord2(sK471),X0) = iProver_top
    | r4_wellord1(sK469,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_wellord2(sK471)) != iProver_top ),
    inference(renaming,[status(thm)],[c_147395])).

cnf(c_147405,plain,
    ( r4_wellord1(k1_wellord2(sK471),X0) = iProver_top
    | r4_wellord1(sK469,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_147396,c_73087])).

cnf(c_2563,plain,
    ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f6620])).

cnf(c_73078,plain,
    ( X0 = X1
    | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0)) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2563])).

cnf(c_147413,plain,
    ( sK471 = X0
    | r4_wellord1(sK469,k1_wellord2(X0)) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK471) != iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_147405,c_73078])).

cnf(c_2568,negated_conjecture,
    ( v3_ordinal1(sK470) ),
    inference(cnf_transformation,[],[f6622])).

cnf(c_2579,plain,
    ( v3_ordinal1(sK470) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2568])).

cnf(c_2567,negated_conjecture,
    ( v3_ordinal1(sK471) ),
    inference(cnf_transformation,[],[f6623])).

cnf(c_2580,plain,
    ( v3_ordinal1(sK471) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2567])).

cnf(c_2564,negated_conjecture,
    ( sK470 != sK471 ),
    inference(cnf_transformation,[],[f6626])).

cnf(c_2631,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2553])).

cnf(c_36289,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_100846,plain,
    ( sK471 != X0
    | sK470 != X0
    | sK470 = sK471 ),
    inference(instantiation,[status(thm)],[c_36289])).

cnf(c_2566,negated_conjecture,
    ( r4_wellord1(sK469,k1_wellord2(sK470)) ),
    inference(cnf_transformation,[],[f6624])).

cnf(c_73076,plain,
    ( r4_wellord1(sK469,k1_wellord2(sK470)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2566])).

cnf(c_143969,plain,
    ( r4_wellord1(k1_wellord2(sK470),sK469) = iProver_top
    | v1_relat_1(k1_wellord2(sK470)) != iProver_top
    | v1_relat_1(sK469) != iProver_top ),
    inference(superposition,[status(thm)],[c_73076,c_73524])).

cnf(c_146470,plain,
    ( v1_relat_1(k1_wellord2(sK470)) != iProver_top
    | r4_wellord1(k1_wellord2(sK470),sK469) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_143969,c_2578])).

cnf(c_146471,plain,
    ( r4_wellord1(k1_wellord2(sK470),sK469) = iProver_top
    | v1_relat_1(k1_wellord2(sK470)) != iProver_top ),
    inference(renaming,[status(thm)],[c_146470])).

cnf(c_146476,plain,
    ( r4_wellord1(k1_wellord2(sK470),sK469) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_146471,c_73087])).

cnf(c_146479,plain,
    ( r4_wellord1(k1_wellord2(sK470),X0) = iProver_top
    | r4_wellord1(sK469,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_wellord2(sK470)) != iProver_top
    | v1_relat_1(sK469) != iProver_top ),
    inference(superposition,[status(thm)],[c_146476,c_73522])).

cnf(c_147482,plain,
    ( v1_relat_1(k1_wellord2(sK470)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | r4_wellord1(sK469,X0) != iProver_top
    | r4_wellord1(k1_wellord2(sK470),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_146479,c_2578])).

cnf(c_147483,plain,
    ( r4_wellord1(k1_wellord2(sK470),X0) = iProver_top
    | r4_wellord1(sK469,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_wellord2(sK470)) != iProver_top ),
    inference(renaming,[status(thm)],[c_147482])).

cnf(c_147492,plain,
    ( r4_wellord1(k1_wellord2(sK470),X0) = iProver_top
    | r4_wellord1(sK469,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_147483,c_73087])).

cnf(c_147500,plain,
    ( sK470 = X0
    | r4_wellord1(sK469,k1_wellord2(X0)) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK470) != iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_147492,c_73078])).

cnf(c_148615,plain,
    ( r4_wellord1(sK469,k1_wellord2(X0)) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_147413,c_2579,c_2580,c_2564,c_2631,c_100846,c_147500])).

cnf(c_148623,plain,
    ( v3_ordinal1(sK471) != iProver_top ),
    inference(superposition,[status(thm)],[c_73077,c_148615])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_148623,c_2580])).

%------------------------------------------------------------------------------
