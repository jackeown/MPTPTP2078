%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0610+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:47 EST 2020

% Result     : Theorem 23.24s
% Output     : CNFRefutation 23.24s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 155 expanded)
%              Number of clauses        :   47 (  54 expanded)
%              Number of leaves         :   17 (  36 expanded)
%              Depth                    :   18
%              Number of atoms          :  264 ( 445 expanded)
%              Number of equality atoms :   69 (  77 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2090,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2242,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f3450,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f2090,f2242,f2242])).

fof(f96,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2227,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f96])).

fof(f824,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1536,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f824])).

fof(f1537,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1536])).

fof(f3357,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1537])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1322,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f3094,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1322])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1963,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f3055,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1963])).

fof(f818,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f819,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f818])).

fof(f1528,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f819])).

fof(f1529,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1528])).

fof(f2073,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
     => ( ~ r1_xboole_0(X0,sK165)
        & r1_xboole_0(k1_relat_1(X0),k1_relat_1(sK165))
        & v1_relat_1(sK165) ) ) ),
    introduced(choice_axiom,[])).

fof(f2072,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK164,X1)
          & r1_xboole_0(k1_relat_1(sK164),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK164) ) ),
    introduced(choice_axiom,[])).

fof(f2074,plain,
    ( ~ r1_xboole_0(sK164,sK165)
    & r1_xboole_0(k1_relat_1(sK164),k1_relat_1(sK165))
    & v1_relat_1(sK165)
    & v1_relat_1(sK164) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK164,sK165])],[f1529,f2073,f2072])).

fof(f3349,plain,(
    r1_xboole_0(k1_relat_1(sK164),k1_relat_1(sK165)) ),
    inference(cnf_transformation,[],[f2074])).

fof(f879,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1600,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f879])).

fof(f2086,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1600])).

fof(f3429,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2086])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2094,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f4019,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f3429,f2094])).

fof(f3347,plain,(
    v1_relat_1(sK164) ),
    inference(cnf_transformation,[],[f2074])).

fof(f787,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k1_relat_1(X2),X0) )
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1484,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ r1_tarski(k1_relat_1(X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f787])).

fof(f1485,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ r1_tarski(k1_relat_1(X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1484])).

fof(f3311,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k7_relat_1(X1,X0))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1485])).

fof(f3348,plain,(
    v1_relat_1(sK165) ),
    inference(cnf_transformation,[],[f2074])).

fof(f629,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1307,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f629])).

fof(f3082,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1307])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f888,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f909,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f888])).

fof(f1662,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK20(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f1663,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK20(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f909,f1662])).

fof(f2144,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK20(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1663])).

fof(f3470,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK20(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f2144,f2242])).

fof(f476,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2845,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f476])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2782,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f3444,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f2782,f2094])).

fof(f3861,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2845,f3444])).

fof(f3350,plain,(
    ~ r1_xboole_0(sK164,sK165) ),
    inference(cnf_transformation,[],[f2074])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3450])).

cnf(c_140,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2227])).

cnf(c_54796,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_69371,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_54796])).

cnf(c_1257,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f3357])).

cnf(c_993,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3094])).

cnf(c_953,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3055])).

cnf(c_6309,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1257,c_993,c_953])).

cnf(c_6310,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_6309])).

cnf(c_54006,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6310])).

cnf(c_1247,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK164),k1_relat_1(sK165)) ),
    inference(cnf_transformation,[],[f3349])).

cnf(c_54077,plain,
    ( r1_xboole_0(k1_relat_1(sK164),k1_relat_1(sK165)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1247])).

cnf(c_1327,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4019])).

cnf(c_54016,plain,
    ( k7_relat_1(X0,X1) = o_0_0_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1327])).

cnf(c_82366,plain,
    ( k7_relat_1(sK164,k1_relat_1(sK165)) = o_0_0_xboole_0
    | v1_relat_1(sK164) != iProver_top ),
    inference(superposition,[status(thm)],[c_54077,c_54016])).

cnf(c_1249,negated_conjecture,
    ( v1_relat_1(sK164) ),
    inference(cnf_transformation,[],[f3347])).

cnf(c_1333,plain,
    ( v1_relat_1(sK164) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1249])).

cnf(c_84936,plain,
    ( k7_relat_1(sK164,k1_relat_1(sK165)) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_82366,c_1333])).

cnf(c_1210,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k7_relat_1(X1,X2))
    | ~ r1_tarski(k1_relat_1(X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3311])).

cnf(c_6377,plain,
    ( ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X0),X2)
    | r1_tarski(X0,k7_relat_1(X1,X2))
    | ~ r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1210,c_993,c_953])).

cnf(c_6378,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k7_relat_1(X1,X2))
    | ~ r1_tarski(k1_relat_1(X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_6377])).

cnf(c_54004,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k7_relat_1(X1,X2)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6378])).

cnf(c_84940,plain,
    ( r1_tarski(X0,sK164) != iProver_top
    | r1_tarski(X0,o_0_0_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(sK165)) != iProver_top
    | v1_relat_1(sK164) != iProver_top ),
    inference(superposition,[status(thm)],[c_84936,c_54004])).

cnf(c_84951,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(sK165)) != iProver_top
    | r1_tarski(X0,o_0_0_xboole_0) = iProver_top
    | r1_tarski(X0,sK164) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_84940,c_1333])).

cnf(c_84952,plain,
    ( r1_tarski(X0,sK164) != iProver_top
    | r1_tarski(X0,o_0_0_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(sK165)) != iProver_top ),
    inference(renaming,[status(thm)],[c_84951])).

cnf(c_84960,plain,
    ( r1_tarski(X0,sK165) != iProver_top
    | r1_tarski(X0,sK164) != iProver_top
    | r1_tarski(X0,o_0_0_xboole_0) = iProver_top
    | v1_relat_1(sK165) != iProver_top ),
    inference(superposition,[status(thm)],[c_54006,c_84952])).

cnf(c_1248,negated_conjecture,
    ( v1_relat_1(sK165) ),
    inference(cnf_transformation,[],[f3348])).

cnf(c_1334,plain,
    ( v1_relat_1(sK165) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1248])).

cnf(c_85938,plain,
    ( r1_tarski(X0,o_0_0_xboole_0) = iProver_top
    | r1_tarski(X0,sK164) != iProver_top
    | r1_tarski(X0,sK165) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_84960,c_1334])).

cnf(c_85939,plain,
    ( r1_tarski(X0,sK165) != iProver_top
    | r1_tarski(X0,sK164) != iProver_top
    | r1_tarski(X0,o_0_0_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_85938])).

cnf(c_85947,plain,
    ( r1_tarski(k4_xboole_0(sK164,X0),sK165) != iProver_top
    | r1_tarski(k4_xboole_0(sK164,X0),o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_54796,c_85939])).

cnf(c_88214,plain,
    ( r1_tarski(k4_xboole_0(sK164,k4_xboole_0(sK164,sK165)),o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_69371,c_85947])).

cnf(c_981,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f3082])).

cnf(c_8850,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_953])).

cnf(c_8851,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_8850])).

cnf(c_10572,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_981,c_8851])).

cnf(c_74851,plain,
    ( ~ r1_tarski(k4_xboole_0(sK164,k4_xboole_0(sK164,sK165)),X0)
    | ~ r2_hidden(sK20(sK164,sK165),k4_xboole_0(sK164,k4_xboole_0(sK164,sK165)))
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_10572])).

cnf(c_74857,plain,
    ( r1_tarski(k4_xboole_0(sK164,k4_xboole_0(sK164,sK165)),X0) != iProver_top
    | r2_hidden(sK20(sK164,sK165),k4_xboole_0(sK164,k4_xboole_0(sK164,sK165))) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74851])).

cnf(c_74859,plain,
    ( r1_tarski(k4_xboole_0(sK164,k4_xboole_0(sK164,sK165)),o_0_0_xboole_0) != iProver_top
    | r2_hidden(sK20(sK164,sK165),k4_xboole_0(sK164,k4_xboole_0(sK164,sK165))) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_74857])).

cnf(c_59,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK20(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f3470])).

cnf(c_64148,plain,
    ( r1_xboole_0(sK164,sK165)
    | r2_hidden(sK20(sK164,sK165),k4_xboole_0(sK164,k4_xboole_0(sK164,sK165))) ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_64149,plain,
    ( r1_xboole_0(sK164,sK165) = iProver_top
    | r2_hidden(sK20(sK164,sK165),k4_xboole_0(sK164,k4_xboole_0(sK164,sK165))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64148])).

cnf(c_745,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3861])).

cnf(c_2786,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_1246,negated_conjecture,
    ( ~ r1_xboole_0(sK164,sK165) ),
    inference(cnf_transformation,[],[f3350])).

cnf(c_1336,plain,
    ( r1_xboole_0(sK164,sK165) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1246])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_88214,c_74859,c_64149,c_2786,c_1336])).

%------------------------------------------------------------------------------
