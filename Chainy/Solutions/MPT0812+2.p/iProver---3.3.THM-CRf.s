%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0812+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:53 EST 2020

% Result     : Theorem 39.20s
% Output     : CNFRefutation 39.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  93 expanded)
%              Number of clauses        :   25 (  27 expanded)
%              Number of leaves         :    6 (  21 expanded)
%              Depth                    :   14
%              Number of atoms          :  223 ( 443 expanded)
%              Number of equality atoms :   50 (  50 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1207,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( v2_wellord1(X0)
              & r4_wellord1(X0,X1) )
           => v2_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1208,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( v2_wellord1(X0)
                & r4_wellord1(X0,X1) )
             => v2_wellord1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f1207])).

fof(f2439,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1208])).

fof(f2440,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f2439])).

fof(f3302,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ v2_wellord1(sK320)
        & v2_wellord1(X0)
        & r4_wellord1(X0,sK320)
        & v1_relat_1(sK320) ) ) ),
    introduced(choice_axiom,[])).

fof(f3301,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_wellord1(X1)
            & v2_wellord1(X0)
            & r4_wellord1(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(sK319)
          & r4_wellord1(sK319,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK319) ) ),
    introduced(choice_axiom,[])).

fof(f3303,plain,
    ( ~ v2_wellord1(sK320)
    & v2_wellord1(sK319)
    & r4_wellord1(sK319,sK320)
    & v1_relat_1(sK320)
    & v1_relat_1(sK319) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK319,sK320])],[f2440,f3302,f3301])).

fof(f5396,plain,(
    r4_wellord1(sK319,sK320) ),
    inference(cnf_transformation,[],[f3303])).

fof(f1140,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( r4_wellord1(X0,X1)
              & v2_wellord1(X0) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( k3_wellord1(X0,X1) = X2
                <=> r3_wellord1(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2329,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k3_wellord1(X0,X1) = X2
              <=> r3_wellord1(X0,X1,X2) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ r4_wellord1(X0,X1)
          | ~ v2_wellord1(X0)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1140])).

fof(f2330,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k3_wellord1(X0,X1) = X2
              <=> r3_wellord1(X0,X1,X2) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ r4_wellord1(X0,X1)
          | ~ v2_wellord1(X0)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2329])).

fof(f3226,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_wellord1(X0,X1) = X2
                  | ~ r3_wellord1(X0,X1,X2) )
                & ( r3_wellord1(X0,X1,X2)
                  | k3_wellord1(X0,X1) != X2 ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ r4_wellord1(X0,X1)
          | ~ v2_wellord1(X0)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2330])).

fof(f5254,plain,(
    ! [X2,X0,X1] :
      ( r3_wellord1(X0,X1,X2)
      | k3_wellord1(X0,X1) != X2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r4_wellord1(X0,X1)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3226])).

fof(f6333,plain,(
    ! [X0,X1] :
      ( r3_wellord1(X0,X1,k3_wellord1(X0,X1))
      | ~ v1_funct_1(k3_wellord1(X0,X1))
      | ~ v1_relat_1(k3_wellord1(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f5254])).

fof(f1143,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k3_wellord1(X0,X1))
        & v1_relat_1(k3_wellord1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2332,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k3_wellord1(X0,X1))
        & v1_relat_1(k3_wellord1(X0,X1)) )
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1143])).

fof(f2333,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k3_wellord1(X0,X1))
        & v1_relat_1(k3_wellord1(X0,X1)) )
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2332])).

fof(f5257,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_wellord1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2333])).

fof(f5258,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_wellord1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2333])).

fof(f1196,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( r3_wellord1(X0,X1,X2)
                  & v2_wellord1(X0) )
               => v2_wellord1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2418,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_wellord1(X1)
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v2_wellord1(X0)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1196])).

fof(f2419,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_wellord1(X1)
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v2_wellord1(X0)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2418])).

fof(f5374,plain,(
    ! [X2,X0,X1] :
      ( v2_wellord1(X1)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v2_wellord1(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2419])).

fof(f5398,plain,(
    ~ v2_wellord1(sK320) ),
    inference(cnf_transformation,[],[f3303])).

fof(f5397,plain,(
    v2_wellord1(sK319) ),
    inference(cnf_transformation,[],[f3303])).

fof(f5395,plain,(
    v1_relat_1(sK320) ),
    inference(cnf_transformation,[],[f3303])).

fof(f5394,plain,(
    v1_relat_1(sK319) ),
    inference(cnf_transformation,[],[f3303])).

cnf(c_2074,negated_conjecture,
    ( r4_wellord1(sK319,sK320) ),
    inference(cnf_transformation,[],[f5396])).

cnf(c_58669,plain,
    ( r4_wellord1(sK319,sK320) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2074])).

cnf(c_1933,plain,
    ( r3_wellord1(X0,X1,k3_wellord1(X0,X1))
    | ~ r4_wellord1(X0,X1)
    | ~ v2_wellord1(X0)
    | ~ v1_funct_1(k3_wellord1(X0,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k3_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f6333])).

cnf(c_1936,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k3_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f5257])).

cnf(c_1935,plain,
    ( v1_funct_1(k3_wellord1(X0,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f5258])).

cnf(c_18159,plain,
    ( ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | r3_wellord1(X0,X1,k3_wellord1(X0,X1))
    | ~ r4_wellord1(X0,X1)
    | ~ v2_wellord1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1933,c_1936,c_1935])).

cnf(c_18160,plain,
    ( r3_wellord1(X0,X1,k3_wellord1(X0,X1))
    | ~ r4_wellord1(X0,X1)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_18159])).

cnf(c_58599,plain,
    ( r3_wellord1(X0,X1,k3_wellord1(X0,X1)) = iProver_top
    | r4_wellord1(X0,X1) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18160])).

cnf(c_2052,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ v2_wellord1(X0)
    | v2_wellord1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f5374])).

cnf(c_58691,plain,
    ( r3_wellord1(X0,X1,X2) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v2_wellord1(X1) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2052])).

cnf(c_83035,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v2_wellord1(X1) = iProver_top
    | v1_funct_1(k3_wellord1(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k3_wellord1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_58599,c_58691])).

cnf(c_2473,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k3_wellord1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1936])).

cnf(c_2476,plain,
    ( v1_funct_1(k3_wellord1(X0,X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1935])).

cnf(c_139656,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | r4_wellord1(X0,X1) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v2_wellord1(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_83035,c_2473,c_2476])).

cnf(c_139657,plain,
    ( r4_wellord1(X0,X1) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v2_wellord1(X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_139656])).

cnf(c_139676,plain,
    ( v2_wellord1(sK319) != iProver_top
    | v2_wellord1(sK320) = iProver_top
    | v1_relat_1(sK319) != iProver_top
    | v1_relat_1(sK320) != iProver_top ),
    inference(superposition,[status(thm)],[c_58669,c_139657])).

cnf(c_2072,negated_conjecture,
    ( ~ v2_wellord1(sK320) ),
    inference(cnf_transformation,[],[f5398])).

cnf(c_2085,plain,
    ( v2_wellord1(sK320) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2072])).

cnf(c_2073,negated_conjecture,
    ( v2_wellord1(sK319) ),
    inference(cnf_transformation,[],[f5397])).

cnf(c_2084,plain,
    ( v2_wellord1(sK319) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2073])).

cnf(c_2075,negated_conjecture,
    ( v1_relat_1(sK320) ),
    inference(cnf_transformation,[],[f5395])).

cnf(c_2082,plain,
    ( v1_relat_1(sK320) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2075])).

cnf(c_2076,negated_conjecture,
    ( v1_relat_1(sK319) ),
    inference(cnf_transformation,[],[f5394])).

cnf(c_2081,plain,
    ( v1_relat_1(sK319) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2076])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_139676,c_2085,c_2084,c_2082,c_2081])).

%------------------------------------------------------------------------------
