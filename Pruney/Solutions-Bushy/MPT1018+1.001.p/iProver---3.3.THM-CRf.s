%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1018+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:40 EST 2020

% Result     : Theorem 0.75s
% Output     : CNFRefutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   49 (  98 expanded)
%              Number of clauses        :   26 (  26 expanded)
%              Number of leaves         :    7 (  28 expanded)
%              Depth                    :   17
%              Number of atoms          :  232 ( 680 expanded)
%              Number of equality atoms :   87 ( 213 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK4 != sK5
        & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5)
        & r2_hidden(sK5,X0)
        & r2_hidden(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X3,X2] :
          ( X2 != X3
          & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3)
          & r2_hidden(X3,sK2)
          & r2_hidden(X2,sK2) )
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( sK4 != sK5
    & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    & r2_hidden(sK5,sK2)
    & r2_hidden(sK4,sK2)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f7,f13,f12])).

fof(f21,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f5,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f4])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_1(X1)
          | ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) ) )
        & ( ! [X2,X3] :
              ( X2 = X3
              | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_1(X1)
          | ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) ) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | ~ v2_funct_1(X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(rectify,[],[f8])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK0(X0,X1) != sK1(X0,X1)
        & k1_funct_1(X1,sK0(X0,X1)) = k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_1(X1)
          | ( sK0(X0,X1) != sK1(X0,X1)
            & k1_funct_1(X1,sK0(X0,X1)) = k1_funct_1(X1,sK1(X0,X1))
            & r2_hidden(sK1(X0,X1),X0)
            & r2_hidden(sK0(X0,X1),X0) ) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | ~ v2_funct_1(X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f15,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f14])).

fof(f27,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_11,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | X2 = X3
    | k1_funct_1(X0,X2) != k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_122,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | X2 = X3
    | k1_funct_1(X0,X2) != k1_funct_1(X0,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_123,plain,
    ( ~ v1_funct_2(sK3,X0,X0)
    | ~ r2_hidden(X1,X0)
    | ~ r2_hidden(X2,X0)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | X2 = X1
    | k1_funct_1(sK3,X2) != k1_funct_1(sK3,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_122])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_127,plain,
    ( ~ v1_funct_2(sK3,X0,X0)
    | ~ r2_hidden(X1,X0)
    | ~ r2_hidden(X2,X0)
    | X2 = X1
    | k1_funct_1(sK3,X2) != k1_funct_1(sK3,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_123,c_12,c_9])).

cnf(c_167,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | X2 = X0
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK2 != X1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_127])).

cnf(c_168,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | X0 = X1
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_167])).

cnf(c_197,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | X0 = X1
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_168])).

cnf(c_220,plain,
    ( ~ r2_hidden(X0_42,sK2)
    | ~ r2_hidden(X1_42,sK2)
    | k1_funct_1(sK3,X1_42) != k1_funct_1(sK3,X0_42)
    | X0_42 = X1_42 ),
    inference(subtyping,[status(esa)],[c_197])).

cnf(c_328,plain,
    ( ~ r2_hidden(X0_42,sK2)
    | ~ r2_hidden(sK5,sK2)
    | k1_funct_1(sK3,X0_42) != k1_funct_1(sK3,sK5)
    | sK5 = X0_42 ),
    inference(instantiation,[status(thm)],[c_220])).

cnf(c_330,plain,
    ( ~ r2_hidden(sK5,sK2)
    | ~ r2_hidden(sK4,sK2)
    | k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK5)
    | sK5 = sK4 ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_228,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_321,plain,
    ( sK5 != X0_42
    | sK4 != X0_42
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_322,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_6,negated_conjecture,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_223,negated_conjecture,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_5,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_224,negated_conjecture,
    ( sK4 != sK5 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_226,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_235,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_7,negated_conjecture,
    ( r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_8,negated_conjecture,
    ( r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_330,c_322,c_223,c_224,c_235,c_7,c_8])).


%------------------------------------------------------------------------------
