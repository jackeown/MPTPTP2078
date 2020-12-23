%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:03 EST 2020

% Result     : Theorem 0.85s
% Output     : CNFRefutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 836 expanded)
%              Number of clauses        :   60 ( 233 expanded)
%              Number of leaves         :    8 ( 222 expanded)
%              Depth                    :   23
%              Number of atoms          :  377 (5758 expanded)
%              Number of equality atoms :  183 (1920 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,plain,(
    ! [X2,X0] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      | ~ sP0(X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X2,X0] :
      ( ( ( v2_funct_1(X2)
          | ? [X3,X4] :
              ( X3 != X4
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
              & r2_hidden(X4,X0)
              & r2_hidden(X3,X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X3,X0) )
          | ~ v2_funct_1(X2) ) )
      | ~ sP0(X2,X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_1(X0)
          | ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X0,X2) = k1_funct_1(X0,X3)
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1) ) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X0,X4) != k1_funct_1(X0,X5)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          | ~ v2_funct_1(X0) ) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X0,X2) = k1_funct_1(X0,X3)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( sK1(X0,X1) != sK2(X0,X1)
        & k1_funct_1(X0,sK1(X0,X1)) = k1_funct_1(X0,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_1(X0)
          | ( sK1(X0,X1) != sK2(X0,X1)
            & k1_funct_1(X0,sK1(X0,X1)) = k1_funct_1(X0,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),X1)
            & r2_hidden(sK1(X0,X1),X1) ) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X0,X4) != k1_funct_1(X0,X5)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          | ~ v2_funct_1(X0) ) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f15])).

fof(f20,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | k1_funct_1(X0,X4) != k1_funct_1(X0,X5)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ v2_funct_1(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,conjecture,(
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

fof(f4,negated_conjecture,(
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
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK5 != sK6
        & k1_funct_1(X1,sK5) = k1_funct_1(X1,sK6)
        & r2_hidden(sK6,X0)
        & r2_hidden(sK5,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
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
          & k1_funct_1(sK4,X2) = k1_funct_1(sK4,X3)
          & r2_hidden(X3,sK3)
          & r2_hidden(X2,sK3) )
      & v2_funct_1(sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
      & v1_funct_2(sK4,sK3,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( sK5 != sK6
    & k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    & r2_hidden(sK6,sK3)
    & r2_hidden(sK5,sK3)
    & v2_funct_1(sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    & v1_funct_2(sK4,sK3,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f10,f18,f17])).

fof(f29,plain,(
    v1_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => ( v2_funct_1(X2)
        <=> ! [X3,X4] :
              ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                & r2_hidden(X4,X0)
                & r2_hidden(X3,X0) )
             => X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( sP0(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f6,f11])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f30,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    r2_hidden(sK6,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    sK5 != sK6 ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(cnf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X2,X1] :
      ( sP0(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f26])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ sP0(X3,X1)
    | ~ v2_funct_1(X3)
    | X0 = X2
    | k1_funct_1(X3,X0) != k1_funct_1(X3,X2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_14,negated_conjecture,
    ( v1_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sP0(X0,X1)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_204,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | sP0(X0,X1)
    | ~ v1_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_205,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | sP0(sK4,X0)
    | ~ v1_funct_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_209,plain,
    ( sP0(sK4,X0)
    | ~ v1_funct_2(sK4,X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_205,c_15])).

cnf(c_210,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | sP0(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_209])).

cnf(c_256,plain,
    ( sP0(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != X0
    | sK3 != X1
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_210])).

cnf(c_257,plain,
    ( sP0(sK4,sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_508,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ v2_funct_1(X3)
    | X0 = X2
    | k1_funct_1(X3,X0) != k1_funct_1(X3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != X1
    | sK3 = k1_xboole_0
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_257])).

cnf(c_509,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X1,sK3)
    | ~ v2_funct_1(sK4)
    | X0 = X1
    | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1)
    | sK3 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_12,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_513,plain,
    ( ~ r2_hidden(X1,sK3)
    | ~ r2_hidden(X0,sK3)
    | X0 = X1
    | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_509,c_12])).

cnf(c_514,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X1,sK3)
    | X0 = X1
    | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1)
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_513])).

cnf(c_590,plain,
    ( ~ r2_hidden(X0_45,sK3)
    | ~ r2_hidden(X1_45,sK3)
    | sK3 = k1_xboole_0
    | X0_45 = X1_45
    | k1_funct_1(sK4,X0_45) != k1_funct_1(sK4,X1_45) ),
    inference(subtyping,[status(esa)],[c_514])).

cnf(c_722,plain,
    ( sK3 = k1_xboole_0
    | X0_45 = X1_45
    | k1_funct_1(sK4,X0_45) != k1_funct_1(sK4,X1_45)
    | r2_hidden(X0_45,sK3) != iProver_top
    | r2_hidden(X1_45,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_11,negated_conjecture,
    ( r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK6,sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_8,negated_conjecture,
    ( sK5 != sK6 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_595,negated_conjecture,
    ( sK5 != sK6 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_9,negated_conjecture,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_594,negated_conjecture,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_777,plain,
    ( ~ r2_hidden(sK6,sK3)
    | ~ r2_hidden(sK5,sK3)
    | sK3 = k1_xboole_0
    | k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_923,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_722,c_11,c_10,c_595,c_594,c_777])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | sP0(X0,k1_xboole_0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_156,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | sP0(X0,k1_xboole_0)
    | ~ v1_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_157,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
    | sP0(sK4,k1_xboole_0)
    | ~ v1_funct_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
    inference(unflattening,[status(thm)],[c_156])).

cnf(c_161,plain,
    ( sP0(sK4,k1_xboole_0)
    | ~ v1_funct_2(sK4,k1_xboole_0,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_157,c_15])).

cnf(c_162,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
    | sP0(sK4,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
    inference(renaming,[status(thm)],[c_161])).

cnf(c_243,plain,
    ( sP0(sK4,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != X0
    | sK3 != k1_xboole_0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_162])).

cnf(c_244,plain,
    ( sP0(sK4,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_243])).

cnf(c_478,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ v2_funct_1(X3)
    | X0 = X2
    | k1_funct_1(X3,X0) != k1_funct_1(X3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0
    | sK4 != X3
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_244])).

cnf(c_479,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0)
    | ~ v2_funct_1(sK4)
    | X1 = X0
    | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_483,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X0,k1_xboole_0)
    | X1 = X0
    | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_12])).

cnf(c_484,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0)
    | X1 = X0
    | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_483])).

cnf(c_591,plain,
    ( ~ r2_hidden(X0_45,k1_xboole_0)
    | ~ r2_hidden(X1_45,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0
    | X1_45 = X0_45
    | k1_funct_1(sK4,X1_45) != k1_funct_1(sK4,X0_45) ),
    inference(subtyping,[status(esa)],[c_484])).

cnf(c_597,plain,
    ( sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_591])).

cnf(c_720,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_621,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_812,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_720,c_11,c_10,c_595,c_594,c_621,c_777])).

cnf(c_926,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_923,c_812])).

cnf(c_933,plain,
    ( sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_926])).

cnf(c_593,negated_conjecture,
    ( r2_hidden(sK6,sK3) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_718,plain,
    ( r2_hidden(sK6,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_928,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_923,c_718])).

cnf(c_592,negated_conjecture,
    ( r2_hidden(sK5,sK3) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_719,plain,
    ( r2_hidden(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_927,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_923,c_719])).

cnf(c_596,plain,
    ( ~ r2_hidden(X0_45,k1_xboole_0)
    | ~ r2_hidden(X1_45,k1_xboole_0)
    | X1_45 = X0_45
    | k1_funct_1(sK4,X1_45) != k1_funct_1(sK4,X0_45)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_591])).

cnf(c_721,plain,
    ( X0_45 = X1_45
    | k1_funct_1(sK4,X0_45) != k1_funct_1(sK4,X1_45)
    | r2_hidden(X0_45,k1_xboole_0) != iProver_top
    | r2_hidden(X1_45,k1_xboole_0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_824,plain,
    ( k1_funct_1(sK4,X0_45) != k1_funct_1(sK4,sK5)
    | sK6 = X0_45
    | r2_hidden(X0_45,k1_xboole_0) != iProver_top
    | r2_hidden(sK6,k1_xboole_0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_594,c_721])).

cnf(c_872,plain,
    ( sK6 = sK5
    | r2_hidden(sK6,k1_xboole_0) != iProver_top
    | r2_hidden(sK5,k1_xboole_0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_824])).

cnf(c_603,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_782,plain,
    ( sK6 != X0_45
    | sK5 != X0_45
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_603])).

cnf(c_783,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_782])).

cnf(c_599,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_615,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_599])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_933,c_928,c_927,c_872,c_783,c_595,c_615])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n018.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:32:42 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 0.85/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.85/0.98  
% 0.85/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.85/0.98  
% 0.85/0.98  ------  iProver source info
% 0.85/0.98  
% 0.85/0.98  git: date: 2020-06-30 10:37:57 +0100
% 0.85/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.85/0.98  git: non_committed_changes: false
% 0.85/0.98  git: last_make_outside_of_git: false
% 0.85/0.98  
% 0.85/0.98  ------ 
% 0.85/0.98  
% 0.85/0.98  ------ Input Options
% 0.85/0.98  
% 0.85/0.98  --out_options                           all
% 0.85/0.98  --tptp_safe_out                         true
% 0.85/0.98  --problem_path                          ""
% 0.85/0.98  --include_path                          ""
% 0.85/0.98  --clausifier                            res/vclausify_rel
% 0.85/0.98  --clausifier_options                    --mode clausify
% 0.85/0.98  --stdin                                 false
% 0.85/0.98  --stats_out                             all
% 0.85/0.98  
% 0.85/0.98  ------ General Options
% 0.85/0.98  
% 0.85/0.98  --fof                                   false
% 0.85/0.98  --time_out_real                         305.
% 0.85/0.98  --time_out_virtual                      -1.
% 0.85/0.98  --symbol_type_check                     false
% 0.85/0.98  --clausify_out                          false
% 0.85/0.98  --sig_cnt_out                           false
% 0.85/0.98  --trig_cnt_out                          false
% 0.85/0.98  --trig_cnt_out_tolerance                1.
% 0.85/0.98  --trig_cnt_out_sk_spl                   false
% 0.85/0.98  --abstr_cl_out                          false
% 0.85/0.98  
% 0.85/0.98  ------ Global Options
% 0.85/0.98  
% 0.85/0.98  --schedule                              default
% 0.85/0.98  --add_important_lit                     false
% 0.85/0.98  --prop_solver_per_cl                    1000
% 0.85/0.98  --min_unsat_core                        false
% 0.85/0.98  --soft_assumptions                      false
% 0.85/0.98  --soft_lemma_size                       3
% 0.85/0.98  --prop_impl_unit_size                   0
% 0.85/0.98  --prop_impl_unit                        []
% 0.85/0.98  --share_sel_clauses                     true
% 0.85/0.98  --reset_solvers                         false
% 0.85/0.98  --bc_imp_inh                            [conj_cone]
% 0.85/0.98  --conj_cone_tolerance                   3.
% 0.85/0.98  --extra_neg_conj                        none
% 0.85/0.98  --large_theory_mode                     true
% 0.85/0.98  --prolific_symb_bound                   200
% 0.85/0.98  --lt_threshold                          2000
% 0.85/0.98  --clause_weak_htbl                      true
% 0.85/0.98  --gc_record_bc_elim                     false
% 0.85/0.98  
% 0.85/0.98  ------ Preprocessing Options
% 0.85/0.98  
% 0.85/0.98  --preprocessing_flag                    true
% 0.85/0.98  --time_out_prep_mult                    0.1
% 0.85/0.98  --splitting_mode                        input
% 0.85/0.98  --splitting_grd                         true
% 0.85/0.98  --splitting_cvd                         false
% 0.85/0.98  --splitting_cvd_svl                     false
% 0.85/0.98  --splitting_nvd                         32
% 0.85/0.98  --sub_typing                            true
% 0.85/0.98  --prep_gs_sim                           true
% 0.85/0.98  --prep_unflatten                        true
% 0.85/0.98  --prep_res_sim                          true
% 0.85/0.98  --prep_upred                            true
% 0.85/0.98  --prep_sem_filter                       exhaustive
% 0.85/0.98  --prep_sem_filter_out                   false
% 0.85/0.98  --pred_elim                             true
% 0.85/0.98  --res_sim_input                         true
% 0.85/0.98  --eq_ax_congr_red                       true
% 0.85/0.98  --pure_diseq_elim                       true
% 0.85/0.98  --brand_transform                       false
% 0.85/0.98  --non_eq_to_eq                          false
% 0.85/0.98  --prep_def_merge                        true
% 0.85/0.98  --prep_def_merge_prop_impl              false
% 0.85/0.98  --prep_def_merge_mbd                    true
% 0.85/0.98  --prep_def_merge_tr_red                 false
% 0.85/0.98  --prep_def_merge_tr_cl                  false
% 0.85/0.98  --smt_preprocessing                     true
% 0.85/0.98  --smt_ac_axioms                         fast
% 0.85/0.98  --preprocessed_out                      false
% 0.85/0.98  --preprocessed_stats                    false
% 0.85/0.98  
% 0.85/0.98  ------ Abstraction refinement Options
% 0.85/0.98  
% 0.85/0.98  --abstr_ref                             []
% 0.85/0.98  --abstr_ref_prep                        false
% 0.85/0.98  --abstr_ref_until_sat                   false
% 0.85/0.98  --abstr_ref_sig_restrict                funpre
% 0.85/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.85/0.98  --abstr_ref_under                       []
% 0.85/0.98  
% 0.85/0.98  ------ SAT Options
% 0.85/0.98  
% 0.85/0.98  --sat_mode                              false
% 0.85/0.98  --sat_fm_restart_options                ""
% 0.85/0.98  --sat_gr_def                            false
% 0.85/0.98  --sat_epr_types                         true
% 0.85/0.98  --sat_non_cyclic_types                  false
% 0.85/0.98  --sat_finite_models                     false
% 0.85/0.98  --sat_fm_lemmas                         false
% 0.85/0.98  --sat_fm_prep                           false
% 0.85/0.98  --sat_fm_uc_incr                        true
% 0.85/0.98  --sat_out_model                         small
% 0.85/0.98  --sat_out_clauses                       false
% 0.85/0.98  
% 0.85/0.98  ------ QBF Options
% 0.85/0.98  
% 0.85/0.98  --qbf_mode                              false
% 0.85/0.98  --qbf_elim_univ                         false
% 0.85/0.98  --qbf_dom_inst                          none
% 0.85/0.98  --qbf_dom_pre_inst                      false
% 0.85/0.98  --qbf_sk_in                             false
% 0.85/0.98  --qbf_pred_elim                         true
% 0.85/0.98  --qbf_split                             512
% 0.85/0.98  
% 0.85/0.98  ------ BMC1 Options
% 0.85/0.98  
% 0.85/0.98  --bmc1_incremental                      false
% 0.85/0.98  --bmc1_axioms                           reachable_all
% 0.85/0.98  --bmc1_min_bound                        0
% 0.85/0.98  --bmc1_max_bound                        -1
% 0.85/0.98  --bmc1_max_bound_default                -1
% 0.85/0.98  --bmc1_symbol_reachability              true
% 0.85/0.98  --bmc1_property_lemmas                  false
% 0.85/0.98  --bmc1_k_induction                      false
% 0.85/0.98  --bmc1_non_equiv_states                 false
% 0.85/0.98  --bmc1_deadlock                         false
% 0.85/0.98  --bmc1_ucm                              false
% 0.85/0.98  --bmc1_add_unsat_core                   none
% 0.85/0.98  --bmc1_unsat_core_children              false
% 0.85/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.85/0.98  --bmc1_out_stat                         full
% 0.85/0.98  --bmc1_ground_init                      false
% 0.85/0.98  --bmc1_pre_inst_next_state              false
% 0.85/0.98  --bmc1_pre_inst_state                   false
% 0.85/0.98  --bmc1_pre_inst_reach_state             false
% 0.85/0.98  --bmc1_out_unsat_core                   false
% 0.85/0.98  --bmc1_aig_witness_out                  false
% 0.85/0.98  --bmc1_verbose                          false
% 0.85/0.98  --bmc1_dump_clauses_tptp                false
% 0.85/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.85/0.98  --bmc1_dump_file                        -
% 0.85/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.85/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.85/0.98  --bmc1_ucm_extend_mode                  1
% 0.85/0.98  --bmc1_ucm_init_mode                    2
% 0.85/0.98  --bmc1_ucm_cone_mode                    none
% 0.85/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.85/0.98  --bmc1_ucm_relax_model                  4
% 0.85/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.85/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.85/0.98  --bmc1_ucm_layered_model                none
% 0.85/0.98  --bmc1_ucm_max_lemma_size               10
% 0.85/0.98  
% 0.85/0.98  ------ AIG Options
% 0.85/0.98  
% 0.85/0.98  --aig_mode                              false
% 0.85/0.98  
% 0.85/0.98  ------ Instantiation Options
% 0.85/0.98  
% 0.85/0.98  --instantiation_flag                    true
% 0.85/0.98  --inst_sos_flag                         false
% 0.85/0.98  --inst_sos_phase                        true
% 0.85/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.85/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.85/0.98  --inst_lit_sel_side                     num_symb
% 0.85/0.98  --inst_solver_per_active                1400
% 0.85/0.98  --inst_solver_calls_frac                1.
% 0.85/0.98  --inst_passive_queue_type               priority_queues
% 0.85/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.85/0.98  --inst_passive_queues_freq              [25;2]
% 0.85/0.98  --inst_dismatching                      true
% 0.85/0.98  --inst_eager_unprocessed_to_passive     true
% 0.85/0.98  --inst_prop_sim_given                   true
% 0.85/0.98  --inst_prop_sim_new                     false
% 0.85/0.98  --inst_subs_new                         false
% 0.85/0.98  --inst_eq_res_simp                      false
% 0.85/0.98  --inst_subs_given                       false
% 0.85/0.98  --inst_orphan_elimination               true
% 0.85/0.98  --inst_learning_loop_flag               true
% 0.85/0.98  --inst_learning_start                   3000
% 0.85/0.98  --inst_learning_factor                  2
% 0.85/0.98  --inst_start_prop_sim_after_learn       3
% 0.85/0.98  --inst_sel_renew                        solver
% 0.85/0.98  --inst_lit_activity_flag                true
% 0.85/0.98  --inst_restr_to_given                   false
% 0.85/0.98  --inst_activity_threshold               500
% 0.85/0.98  --inst_out_proof                        true
% 0.85/0.98  
% 0.85/0.98  ------ Resolution Options
% 0.85/0.98  
% 0.85/0.98  --resolution_flag                       true
% 0.85/0.98  --res_lit_sel                           adaptive
% 0.85/0.98  --res_lit_sel_side                      none
% 0.85/0.98  --res_ordering                          kbo
% 0.85/0.98  --res_to_prop_solver                    active
% 0.85/0.98  --res_prop_simpl_new                    false
% 0.85/0.98  --res_prop_simpl_given                  true
% 0.85/0.98  --res_passive_queue_type                priority_queues
% 0.85/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.85/0.98  --res_passive_queues_freq               [15;5]
% 0.85/0.98  --res_forward_subs                      full
% 0.85/0.98  --res_backward_subs                     full
% 0.85/0.98  --res_forward_subs_resolution           true
% 0.85/0.98  --res_backward_subs_resolution          true
% 0.85/0.98  --res_orphan_elimination                true
% 0.85/0.98  --res_time_limit                        2.
% 0.85/0.98  --res_out_proof                         true
% 0.85/0.98  
% 0.85/0.98  ------ Superposition Options
% 0.85/0.98  
% 0.85/0.98  --superposition_flag                    true
% 0.85/0.98  --sup_passive_queue_type                priority_queues
% 0.85/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.85/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.85/0.98  --demod_completeness_check              fast
% 0.85/0.98  --demod_use_ground                      true
% 0.85/0.98  --sup_to_prop_solver                    passive
% 0.85/0.98  --sup_prop_simpl_new                    true
% 0.85/0.98  --sup_prop_simpl_given                  true
% 0.85/0.98  --sup_fun_splitting                     false
% 0.85/0.98  --sup_smt_interval                      50000
% 0.85/0.98  
% 0.85/0.98  ------ Superposition Simplification Setup
% 0.85/0.98  
% 0.85/0.98  --sup_indices_passive                   []
% 0.85/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.85/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.85/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.85/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.85/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.85/0.98  --sup_full_bw                           [BwDemod]
% 0.85/0.98  --sup_immed_triv                        [TrivRules]
% 0.85/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.85/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.85/0.98  --sup_immed_bw_main                     []
% 0.85/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.85/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.85/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.85/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.85/0.98  
% 0.85/0.98  ------ Combination Options
% 0.85/0.98  
% 0.85/0.98  --comb_res_mult                         3
% 0.85/0.98  --comb_sup_mult                         2
% 0.85/0.98  --comb_inst_mult                        10
% 0.85/0.98  
% 0.85/0.98  ------ Debug Options
% 0.85/0.98  
% 0.85/0.98  --dbg_backtrace                         false
% 0.85/0.98  --dbg_dump_prop_clauses                 false
% 0.85/0.98  --dbg_dump_prop_clauses_file            -
% 0.85/0.98  --dbg_out_stat                          false
% 0.85/0.98  ------ Parsing...
% 0.85/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.85/0.98  
% 0.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 0.85/0.98  
% 0.85/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.85/0.98  
% 0.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.85/0.98  ------ Proving...
% 0.85/0.98  ------ Problem Properties 
% 0.85/0.98  
% 0.85/0.98  
% 0.85/0.98  clauses                                 8
% 0.85/0.98  conjectures                             4
% 0.85/0.98  EPR                                     3
% 0.85/0.98  Horn                                    6
% 0.85/0.98  unary                                   4
% 0.85/0.98  binary                                  0
% 0.85/0.98  lits                                    20
% 0.85/0.98  lits eq                                 11
% 0.85/0.98  fd_pure                                 0
% 0.85/0.98  fd_pseudo                               0
% 0.85/0.98  fd_cond                                 0
% 0.85/0.98  fd_pseudo_cond                          2
% 0.85/0.98  AC symbols                              0
% 0.85/0.98  
% 0.85/0.98  ------ Schedule dynamic 5 is on 
% 0.85/0.98  
% 0.85/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.85/0.98  
% 0.85/0.98  
% 0.85/0.98  ------ 
% 0.85/0.98  Current options:
% 0.85/0.98  ------ 
% 0.85/0.98  
% 0.85/0.98  ------ Input Options
% 0.85/0.98  
% 0.85/0.98  --out_options                           all
% 0.85/0.98  --tptp_safe_out                         true
% 0.85/0.98  --problem_path                          ""
% 0.85/0.98  --include_path                          ""
% 0.85/0.98  --clausifier                            res/vclausify_rel
% 0.85/0.98  --clausifier_options                    --mode clausify
% 0.85/0.98  --stdin                                 false
% 0.85/0.98  --stats_out                             all
% 0.85/0.98  
% 0.85/0.98  ------ General Options
% 0.85/0.98  
% 0.85/0.98  --fof                                   false
% 0.85/0.98  --time_out_real                         305.
% 0.85/0.98  --time_out_virtual                      -1.
% 0.85/0.98  --symbol_type_check                     false
% 0.85/0.98  --clausify_out                          false
% 0.85/0.98  --sig_cnt_out                           false
% 0.85/0.98  --trig_cnt_out                          false
% 0.85/0.98  --trig_cnt_out_tolerance                1.
% 0.85/0.98  --trig_cnt_out_sk_spl                   false
% 0.85/0.98  --abstr_cl_out                          false
% 0.85/0.98  
% 0.85/0.98  ------ Global Options
% 0.85/0.98  
% 0.85/0.98  --schedule                              default
% 0.85/0.98  --add_important_lit                     false
% 0.85/0.98  --prop_solver_per_cl                    1000
% 0.85/0.98  --min_unsat_core                        false
% 0.85/0.98  --soft_assumptions                      false
% 0.85/0.98  --soft_lemma_size                       3
% 0.85/0.98  --prop_impl_unit_size                   0
% 0.85/0.98  --prop_impl_unit                        []
% 0.85/0.98  --share_sel_clauses                     true
% 0.85/0.98  --reset_solvers                         false
% 0.85/0.98  --bc_imp_inh                            [conj_cone]
% 0.85/0.98  --conj_cone_tolerance                   3.
% 0.85/0.98  --extra_neg_conj                        none
% 0.85/0.98  --large_theory_mode                     true
% 0.85/0.98  --prolific_symb_bound                   200
% 0.85/0.98  --lt_threshold                          2000
% 0.85/0.98  --clause_weak_htbl                      true
% 0.85/0.98  --gc_record_bc_elim                     false
% 0.85/0.98  
% 0.85/0.98  ------ Preprocessing Options
% 0.85/0.98  
% 0.85/0.98  --preprocessing_flag                    true
% 0.85/0.98  --time_out_prep_mult                    0.1
% 0.85/0.98  --splitting_mode                        input
% 0.85/0.98  --splitting_grd                         true
% 0.85/0.98  --splitting_cvd                         false
% 0.85/0.98  --splitting_cvd_svl                     false
% 0.85/0.98  --splitting_nvd                         32
% 0.85/0.98  --sub_typing                            true
% 0.85/0.98  --prep_gs_sim                           true
% 0.85/0.98  --prep_unflatten                        true
% 0.85/0.98  --prep_res_sim                          true
% 0.85/0.98  --prep_upred                            true
% 0.85/0.98  --prep_sem_filter                       exhaustive
% 0.85/0.98  --prep_sem_filter_out                   false
% 0.85/0.98  --pred_elim                             true
% 0.85/0.98  --res_sim_input                         true
% 0.85/0.98  --eq_ax_congr_red                       true
% 0.85/0.98  --pure_diseq_elim                       true
% 0.85/0.98  --brand_transform                       false
% 0.85/0.98  --non_eq_to_eq                          false
% 0.85/0.98  --prep_def_merge                        true
% 0.85/0.98  --prep_def_merge_prop_impl              false
% 0.85/0.98  --prep_def_merge_mbd                    true
% 0.85/0.98  --prep_def_merge_tr_red                 false
% 0.85/0.98  --prep_def_merge_tr_cl                  false
% 0.85/0.98  --smt_preprocessing                     true
% 0.85/0.98  --smt_ac_axioms                         fast
% 0.85/0.98  --preprocessed_out                      false
% 0.85/0.98  --preprocessed_stats                    false
% 0.85/0.98  
% 0.85/0.98  ------ Abstraction refinement Options
% 0.85/0.98  
% 0.85/0.98  --abstr_ref                             []
% 0.85/0.98  --abstr_ref_prep                        false
% 0.85/0.98  --abstr_ref_until_sat                   false
% 0.85/0.98  --abstr_ref_sig_restrict                funpre
% 0.85/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.85/0.98  --abstr_ref_under                       []
% 0.85/0.98  
% 0.85/0.98  ------ SAT Options
% 0.85/0.98  
% 0.85/0.98  --sat_mode                              false
% 0.85/0.98  --sat_fm_restart_options                ""
% 0.85/0.98  --sat_gr_def                            false
% 0.85/0.98  --sat_epr_types                         true
% 0.85/0.98  --sat_non_cyclic_types                  false
% 0.85/0.98  --sat_finite_models                     false
% 0.85/0.98  --sat_fm_lemmas                         false
% 0.85/0.98  --sat_fm_prep                           false
% 0.85/0.98  --sat_fm_uc_incr                        true
% 0.85/0.98  --sat_out_model                         small
% 0.85/0.98  --sat_out_clauses                       false
% 0.85/0.98  
% 0.85/0.98  ------ QBF Options
% 0.85/0.98  
% 0.85/0.98  --qbf_mode                              false
% 0.85/0.98  --qbf_elim_univ                         false
% 0.85/0.98  --qbf_dom_inst                          none
% 0.85/0.98  --qbf_dom_pre_inst                      false
% 0.85/0.98  --qbf_sk_in                             false
% 0.85/0.98  --qbf_pred_elim                         true
% 0.85/0.98  --qbf_split                             512
% 0.85/0.98  
% 0.85/0.98  ------ BMC1 Options
% 0.85/0.98  
% 0.85/0.98  --bmc1_incremental                      false
% 0.85/0.98  --bmc1_axioms                           reachable_all
% 0.85/0.98  --bmc1_min_bound                        0
% 0.85/0.98  --bmc1_max_bound                        -1
% 0.85/0.98  --bmc1_max_bound_default                -1
% 0.85/0.98  --bmc1_symbol_reachability              true
% 0.85/0.98  --bmc1_property_lemmas                  false
% 0.85/0.98  --bmc1_k_induction                      false
% 0.85/0.98  --bmc1_non_equiv_states                 false
% 0.85/0.98  --bmc1_deadlock                         false
% 0.85/0.98  --bmc1_ucm                              false
% 0.85/0.98  --bmc1_add_unsat_core                   none
% 0.85/0.98  --bmc1_unsat_core_children              false
% 0.85/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.85/0.98  --bmc1_out_stat                         full
% 0.85/0.98  --bmc1_ground_init                      false
% 0.85/0.98  --bmc1_pre_inst_next_state              false
% 0.85/0.98  --bmc1_pre_inst_state                   false
% 0.85/0.98  --bmc1_pre_inst_reach_state             false
% 0.85/0.98  --bmc1_out_unsat_core                   false
% 0.85/0.98  --bmc1_aig_witness_out                  false
% 0.85/0.98  --bmc1_verbose                          false
% 0.85/0.98  --bmc1_dump_clauses_tptp                false
% 0.85/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.85/0.98  --bmc1_dump_file                        -
% 0.85/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.85/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.85/0.98  --bmc1_ucm_extend_mode                  1
% 0.85/0.98  --bmc1_ucm_init_mode                    2
% 0.85/0.98  --bmc1_ucm_cone_mode                    none
% 0.85/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.85/0.98  --bmc1_ucm_relax_model                  4
% 0.85/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.85/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.85/0.98  --bmc1_ucm_layered_model                none
% 0.85/0.98  --bmc1_ucm_max_lemma_size               10
% 0.85/0.98  
% 0.85/0.98  ------ AIG Options
% 0.85/0.98  
% 0.85/0.98  --aig_mode                              false
% 0.85/0.98  
% 0.85/0.98  ------ Instantiation Options
% 0.85/0.98  
% 0.85/0.98  --instantiation_flag                    true
% 0.85/0.98  --inst_sos_flag                         false
% 0.85/0.98  --inst_sos_phase                        true
% 0.85/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.85/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.85/0.98  --inst_lit_sel_side                     none
% 0.85/0.98  --inst_solver_per_active                1400
% 0.85/0.98  --inst_solver_calls_frac                1.
% 0.85/0.98  --inst_passive_queue_type               priority_queues
% 0.85/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.85/0.98  --inst_passive_queues_freq              [25;2]
% 0.85/0.98  --inst_dismatching                      true
% 0.85/0.98  --inst_eager_unprocessed_to_passive     true
% 0.85/0.98  --inst_prop_sim_given                   true
% 0.85/0.98  --inst_prop_sim_new                     false
% 0.85/0.98  --inst_subs_new                         false
% 0.85/0.98  --inst_eq_res_simp                      false
% 0.85/0.98  --inst_subs_given                       false
% 0.85/0.98  --inst_orphan_elimination               true
% 0.85/0.98  --inst_learning_loop_flag               true
% 0.85/0.98  --inst_learning_start                   3000
% 0.85/0.98  --inst_learning_factor                  2
% 0.85/0.98  --inst_start_prop_sim_after_learn       3
% 0.85/0.98  --inst_sel_renew                        solver
% 0.85/0.98  --inst_lit_activity_flag                true
% 0.85/0.98  --inst_restr_to_given                   false
% 0.85/0.98  --inst_activity_threshold               500
% 0.85/0.98  --inst_out_proof                        true
% 0.85/0.98  
% 0.85/0.98  ------ Resolution Options
% 0.85/0.98  
% 0.85/0.98  --resolution_flag                       false
% 0.85/0.98  --res_lit_sel                           adaptive
% 0.85/0.98  --res_lit_sel_side                      none
% 0.85/0.98  --res_ordering                          kbo
% 0.85/0.98  --res_to_prop_solver                    active
% 0.85/0.98  --res_prop_simpl_new                    false
% 0.85/0.98  --res_prop_simpl_given                  true
% 0.85/0.98  --res_passive_queue_type                priority_queues
% 0.85/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.85/0.98  --res_passive_queues_freq               [15;5]
% 0.85/0.98  --res_forward_subs                      full
% 0.85/0.98  --res_backward_subs                     full
% 0.85/0.98  --res_forward_subs_resolution           true
% 0.85/0.98  --res_backward_subs_resolution          true
% 0.85/0.98  --res_orphan_elimination                true
% 0.85/0.98  --res_time_limit                        2.
% 0.85/0.98  --res_out_proof                         true
% 0.85/0.98  
% 0.85/0.98  ------ Superposition Options
% 0.85/0.98  
% 0.85/0.98  --superposition_flag                    true
% 0.85/0.98  --sup_passive_queue_type                priority_queues
% 0.85/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.85/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.85/0.98  --demod_completeness_check              fast
% 0.85/0.98  --demod_use_ground                      true
% 0.85/0.98  --sup_to_prop_solver                    passive
% 0.85/0.98  --sup_prop_simpl_new                    true
% 0.85/0.98  --sup_prop_simpl_given                  true
% 0.85/0.98  --sup_fun_splitting                     false
% 0.85/0.98  --sup_smt_interval                      50000
% 0.85/0.98  
% 0.85/0.98  ------ Superposition Simplification Setup
% 0.85/0.98  
% 0.85/0.98  --sup_indices_passive                   []
% 0.85/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.85/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.85/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.85/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.85/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.85/0.98  --sup_full_bw                           [BwDemod]
% 0.85/0.98  --sup_immed_triv                        [TrivRules]
% 0.85/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.85/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.85/0.98  --sup_immed_bw_main                     []
% 0.85/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.85/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.85/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.85/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.85/0.98  
% 0.85/0.98  ------ Combination Options
% 0.85/0.98  
% 0.85/0.98  --comb_res_mult                         3
% 0.85/0.98  --comb_sup_mult                         2
% 0.85/0.98  --comb_inst_mult                        10
% 0.85/0.98  
% 0.85/0.98  ------ Debug Options
% 0.85/0.98  
% 0.85/0.98  --dbg_backtrace                         false
% 0.85/0.98  --dbg_dump_prop_clauses                 false
% 0.85/0.98  --dbg_dump_prop_clauses_file            -
% 0.85/0.98  --dbg_out_stat                          false
% 0.85/0.98  
% 0.85/0.98  
% 0.85/0.98  
% 0.85/0.98  
% 0.85/0.98  ------ Proving...
% 0.85/0.98  
% 0.85/0.98  
% 0.85/0.98  % SZS status Theorem for theBenchmark.p
% 0.85/0.98  
% 0.85/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 0.85/0.98  
% 0.85/0.98  fof(f11,plain,(
% 0.85/0.98    ! [X2,X0] : ((v2_funct_1(X2) <=> ! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0))) | ~sP0(X2,X0))),
% 0.85/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.85/0.98  
% 0.85/0.98  fof(f13,plain,(
% 0.85/0.98    ! [X2,X0] : (((v2_funct_1(X2) | ? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | ~v2_funct_1(X2))) | ~sP0(X2,X0))),
% 0.85/0.98    inference(nnf_transformation,[],[f11])).
% 0.85/0.98  
% 0.85/0.98  fof(f14,plain,(
% 0.85/0.98    ! [X0,X1] : (((v2_funct_1(X0) | ? [X2,X3] : (X2 != X3 & k1_funct_1(X0,X2) = k1_funct_1(X0,X3) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X0,X4) != k1_funct_1(X0,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~v2_funct_1(X0))) | ~sP0(X0,X1))),
% 0.85/0.98    inference(rectify,[],[f13])).
% 0.85/0.98  
% 0.85/0.98  fof(f15,plain,(
% 0.85/0.98    ! [X1,X0] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X0,X2) = k1_funct_1(X0,X3) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (sK1(X0,X1) != sK2(X0,X1) & k1_funct_1(X0,sK1(X0,X1)) = k1_funct_1(X0,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK1(X0,X1),X1)))),
% 0.85/0.98    introduced(choice_axiom,[])).
% 0.85/0.98  
% 0.85/0.98  fof(f16,plain,(
% 0.85/0.98    ! [X0,X1] : (((v2_funct_1(X0) | (sK1(X0,X1) != sK2(X0,X1) & k1_funct_1(X0,sK1(X0,X1)) = k1_funct_1(X0,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK1(X0,X1),X1))) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X0,X4) != k1_funct_1(X0,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~v2_funct_1(X0))) | ~sP0(X0,X1))),
% 0.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f15])).
% 0.85/0.98  
% 0.85/0.98  fof(f20,plain,(
% 0.85/0.98    ( ! [X4,X0,X5,X1] : (X4 = X5 | k1_funct_1(X0,X4) != k1_funct_1(X0,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~v2_funct_1(X0) | ~sP0(X0,X1)) )),
% 0.85/0.98    inference(cnf_transformation,[],[f16])).
% 0.85/0.98  
% 0.85/0.98  fof(f3,conjecture,(
% 0.85/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.85/0.98  
% 0.85/0.98  fof(f4,negated_conjecture,(
% 0.85/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.85/0.98    inference(negated_conjecture,[],[f3])).
% 0.85/0.98  
% 0.85/0.98  fof(f9,plain,(
% 0.85/0.98    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.85/0.98    inference(ennf_transformation,[],[f4])).
% 0.85/0.98  
% 0.85/0.98  fof(f10,plain,(
% 0.85/0.98    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.85/0.98    inference(flattening,[],[f9])).
% 0.85/0.98  
% 0.85/0.98  fof(f18,plain,(
% 0.85/0.98    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK5 != sK6 & k1_funct_1(X1,sK5) = k1_funct_1(X1,sK6) & r2_hidden(sK6,X0) & r2_hidden(sK5,X0))) )),
% 0.85/0.98    introduced(choice_axiom,[])).
% 0.85/0.98  
% 0.85/0.98  fof(f17,plain,(
% 0.85/0.98    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK4,X2) = k1_funct_1(sK4,X3) & r2_hidden(X3,sK3) & r2_hidden(X2,sK3)) & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4))),
% 0.85/0.98    introduced(choice_axiom,[])).
% 0.85/0.98  
% 0.85/0.98  fof(f19,plain,(
% 0.85/0.98    (sK5 != sK6 & k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) & r2_hidden(sK6,sK3) & r2_hidden(sK5,sK3)) & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4)),
% 0.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f10,f18,f17])).
% 0.85/0.98  
% 0.85/0.98  fof(f29,plain,(
% 0.85/0.98    v1_funct_2(sK4,sK3,sK3)),
% 0.85/0.98    inference(cnf_transformation,[],[f19])).
% 0.85/0.98  
% 0.85/0.98  fof(f1,axiom,(
% 0.85/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v2_funct_1(X2) <=> ! [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) => X3 = X4))))),
% 0.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.85/0.98  
% 0.85/0.98  fof(f5,plain,(
% 0.85/0.98    ! [X0,X1,X2] : (((v2_funct_1(X2) <=> ! [X3,X4] : (X3 = X4 | (k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.85/0.98    inference(ennf_transformation,[],[f1])).
% 0.85/0.98  
% 0.85/0.98  fof(f6,plain,(
% 0.85/0.98    ! [X0,X1,X2] : ((v2_funct_1(X2) <=> ! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.85/0.98    inference(flattening,[],[f5])).
% 0.85/0.98  
% 0.85/0.98  fof(f12,plain,(
% 0.85/0.98    ! [X0,X1,X2] : (sP0(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.85/0.98    inference(definition_folding,[],[f6,f11])).
% 0.85/0.98  
% 0.85/0.98  fof(f25,plain,(
% 0.85/0.98    ( ! [X2,X0,X1] : (sP0(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.85/0.98    inference(cnf_transformation,[],[f12])).
% 0.85/0.98  
% 0.85/0.98  fof(f30,plain,(
% 0.85/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))),
% 0.85/0.98    inference(cnf_transformation,[],[f19])).
% 0.85/0.98  
% 0.85/0.98  fof(f28,plain,(
% 0.85/0.98    v1_funct_1(sK4)),
% 0.85/0.98    inference(cnf_transformation,[],[f19])).
% 0.85/0.98  
% 0.85/0.98  fof(f31,plain,(
% 0.85/0.98    v2_funct_1(sK4)),
% 0.85/0.98    inference(cnf_transformation,[],[f19])).
% 0.85/0.98  
% 0.85/0.98  fof(f32,plain,(
% 0.85/0.98    r2_hidden(sK5,sK3)),
% 0.85/0.98    inference(cnf_transformation,[],[f19])).
% 0.85/0.98  
% 0.85/0.98  fof(f33,plain,(
% 0.85/0.98    r2_hidden(sK6,sK3)),
% 0.85/0.98    inference(cnf_transformation,[],[f19])).
% 0.85/0.98  
% 0.85/0.98  fof(f35,plain,(
% 0.85/0.98    sK5 != sK6),
% 0.85/0.98    inference(cnf_transformation,[],[f19])).
% 0.85/0.98  
% 0.85/0.98  fof(f34,plain,(
% 0.85/0.98    k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)),
% 0.85/0.98    inference(cnf_transformation,[],[f19])).
% 0.85/0.98  
% 0.85/0.98  fof(f26,plain,(
% 0.85/0.98    ( ! [X2,X0,X1] : (sP0(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.85/0.98    inference(cnf_transformation,[],[f12])).
% 0.85/0.98  
% 0.85/0.98  fof(f36,plain,(
% 0.85/0.98    ( ! [X2,X1] : (sP0(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.85/0.98    inference(equality_resolution,[],[f26])).
% 0.85/0.98  
% 0.85/0.98  cnf(c_4,plain,
% 0.85/0.98      ( ~ r2_hidden(X0,X1)
% 0.85/0.98      | ~ r2_hidden(X2,X1)
% 0.85/0.98      | ~ sP0(X3,X1)
% 0.85/0.98      | ~ v2_funct_1(X3)
% 0.85/0.98      | X0 = X2
% 0.85/0.98      | k1_funct_1(X3,X0) != k1_funct_1(X3,X2) ),
% 0.85/0.98      inference(cnf_transformation,[],[f20]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_14,negated_conjecture,
% 0.85/0.98      ( v1_funct_2(sK4,sK3,sK3) ),
% 0.85/0.98      inference(cnf_transformation,[],[f29]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_6,plain,
% 0.85/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 0.85/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.85/0.98      | sP0(X0,X1)
% 0.85/0.98      | ~ v1_funct_1(X0)
% 0.85/0.98      | k1_xboole_0 = X2 ),
% 0.85/0.98      inference(cnf_transformation,[],[f25]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_13,negated_conjecture,
% 0.85/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
% 0.85/0.98      inference(cnf_transformation,[],[f30]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_204,plain,
% 0.85/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 0.85/0.98      | sP0(X0,X1)
% 0.85/0.98      | ~ v1_funct_1(X0)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | sK4 != X0
% 0.85/0.98      | k1_xboole_0 = X2 ),
% 0.85/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_205,plain,
% 0.85/0.98      ( ~ v1_funct_2(sK4,X0,X1)
% 0.85/0.98      | sP0(sK4,X0)
% 0.85/0.98      | ~ v1_funct_1(sK4)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | k1_xboole_0 = X1 ),
% 0.85/0.98      inference(unflattening,[status(thm)],[c_204]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_15,negated_conjecture,
% 0.85/0.98      ( v1_funct_1(sK4) ),
% 0.85/0.98      inference(cnf_transformation,[],[f28]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_209,plain,
% 0.85/0.98      ( sP0(sK4,X0)
% 0.85/0.98      | ~ v1_funct_2(sK4,X0,X1)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | k1_xboole_0 = X1 ),
% 0.85/0.98      inference(global_propositional_subsumption,
% 0.85/0.98                [status(thm)],
% 0.85/0.98                [c_205,c_15]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_210,plain,
% 0.85/0.98      ( ~ v1_funct_2(sK4,X0,X1)
% 0.85/0.98      | sP0(sK4,X0)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | k1_xboole_0 = X1 ),
% 0.85/0.98      inference(renaming,[status(thm)],[c_209]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_256,plain,
% 0.85/0.98      ( sP0(sK4,X0)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | sK3 != X0
% 0.85/0.98      | sK3 != X1
% 0.85/0.98      | sK4 != sK4
% 0.85/0.98      | k1_xboole_0 = X1 ),
% 0.85/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_210]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_257,plain,
% 0.85/0.98      ( sP0(sK4,sK3)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | k1_xboole_0 = sK3 ),
% 0.85/0.98      inference(unflattening,[status(thm)],[c_256]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_508,plain,
% 0.85/0.98      ( ~ r2_hidden(X0,X1)
% 0.85/0.98      | ~ r2_hidden(X2,X1)
% 0.85/0.98      | ~ v2_funct_1(X3)
% 0.85/0.98      | X0 = X2
% 0.85/0.98      | k1_funct_1(X3,X0) != k1_funct_1(X3,X2)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | sK3 != X1
% 0.85/0.98      | sK3 = k1_xboole_0
% 0.85/0.98      | sK4 != X3 ),
% 0.85/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_257]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_509,plain,
% 0.85/0.98      ( ~ r2_hidden(X0,sK3)
% 0.85/0.98      | ~ r2_hidden(X1,sK3)
% 0.85/0.98      | ~ v2_funct_1(sK4)
% 0.85/0.98      | X0 = X1
% 0.85/0.98      | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1)
% 0.85/0.98      | sK3 = k1_xboole_0 ),
% 0.85/0.98      inference(unflattening,[status(thm)],[c_508]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_12,negated_conjecture,
% 0.85/0.98      ( v2_funct_1(sK4) ),
% 0.85/0.98      inference(cnf_transformation,[],[f31]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_513,plain,
% 0.85/0.98      ( ~ r2_hidden(X1,sK3)
% 0.85/0.98      | ~ r2_hidden(X0,sK3)
% 0.85/0.98      | X0 = X1
% 0.85/0.98      | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1)
% 0.85/0.98      | sK3 = k1_xboole_0 ),
% 0.85/0.98      inference(global_propositional_subsumption,
% 0.85/0.98                [status(thm)],
% 0.85/0.98                [c_509,c_12]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_514,plain,
% 0.85/0.98      ( ~ r2_hidden(X0,sK3)
% 0.85/0.98      | ~ r2_hidden(X1,sK3)
% 0.85/0.98      | X0 = X1
% 0.85/0.98      | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1)
% 0.85/0.98      | sK3 = k1_xboole_0 ),
% 0.85/0.98      inference(renaming,[status(thm)],[c_513]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_590,plain,
% 0.85/0.98      ( ~ r2_hidden(X0_45,sK3)
% 0.85/0.98      | ~ r2_hidden(X1_45,sK3)
% 0.85/0.98      | sK3 = k1_xboole_0
% 0.85/0.98      | X0_45 = X1_45
% 0.85/0.98      | k1_funct_1(sK4,X0_45) != k1_funct_1(sK4,X1_45) ),
% 0.85/0.98      inference(subtyping,[status(esa)],[c_514]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_722,plain,
% 0.85/0.98      ( sK3 = k1_xboole_0
% 0.85/0.98      | X0_45 = X1_45
% 0.85/0.98      | k1_funct_1(sK4,X0_45) != k1_funct_1(sK4,X1_45)
% 0.85/0.98      | r2_hidden(X0_45,sK3) != iProver_top
% 0.85/0.98      | r2_hidden(X1_45,sK3) != iProver_top ),
% 0.85/0.98      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_11,negated_conjecture,
% 0.85/0.98      ( r2_hidden(sK5,sK3) ),
% 0.85/0.98      inference(cnf_transformation,[],[f32]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_10,negated_conjecture,
% 0.85/0.98      ( r2_hidden(sK6,sK3) ),
% 0.85/0.98      inference(cnf_transformation,[],[f33]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_8,negated_conjecture,
% 0.85/0.98      ( sK5 != sK6 ),
% 0.85/0.98      inference(cnf_transformation,[],[f35]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_595,negated_conjecture,
% 0.85/0.98      ( sK5 != sK6 ),
% 0.85/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_9,negated_conjecture,
% 0.85/0.98      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
% 0.85/0.98      inference(cnf_transformation,[],[f34]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_594,negated_conjecture,
% 0.85/0.98      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
% 0.85/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_777,plain,
% 0.85/0.98      ( ~ r2_hidden(sK6,sK3)
% 0.85/0.98      | ~ r2_hidden(sK5,sK3)
% 0.85/0.98      | sK3 = k1_xboole_0
% 0.85/0.98      | k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
% 0.85/0.98      | sK5 = sK6 ),
% 0.85/0.98      inference(instantiation,[status(thm)],[c_590]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_923,plain,
% 0.85/0.98      ( sK3 = k1_xboole_0 ),
% 0.85/0.98      inference(global_propositional_subsumption,
% 0.85/0.98                [status(thm)],
% 0.85/0.98                [c_722,c_11,c_10,c_595,c_594,c_777]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_5,plain,
% 0.85/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 0.85/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 0.85/0.98      | sP0(X0,k1_xboole_0)
% 0.85/0.98      | ~ v1_funct_1(X0) ),
% 0.85/0.98      inference(cnf_transformation,[],[f36]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_156,plain,
% 0.85/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 0.85/0.98      | sP0(X0,k1_xboole_0)
% 0.85/0.98      | ~ v1_funct_1(X0)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | sK4 != X0 ),
% 0.85/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_13]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_157,plain,
% 0.85/0.98      ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
% 0.85/0.98      | sP0(sK4,k1_xboole_0)
% 0.85/0.98      | ~ v1_funct_1(sK4)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
% 0.85/0.98      inference(unflattening,[status(thm)],[c_156]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_161,plain,
% 0.85/0.98      ( sP0(sK4,k1_xboole_0)
% 0.85/0.98      | ~ v1_funct_2(sK4,k1_xboole_0,X0)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
% 0.85/0.98      inference(global_propositional_subsumption,
% 0.85/0.98                [status(thm)],
% 0.85/0.98                [c_157,c_15]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_162,plain,
% 0.85/0.98      ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
% 0.85/0.98      | sP0(sK4,k1_xboole_0)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
% 0.85/0.98      inference(renaming,[status(thm)],[c_161]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_243,plain,
% 0.85/0.98      ( sP0(sK4,k1_xboole_0)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | sK3 != X0
% 0.85/0.98      | sK3 != k1_xboole_0
% 0.85/0.98      | sK4 != sK4 ),
% 0.85/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_162]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_244,plain,
% 0.85/0.98      ( sP0(sK4,k1_xboole_0)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | sK3 != k1_xboole_0 ),
% 0.85/0.98      inference(unflattening,[status(thm)],[c_243]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_478,plain,
% 0.85/0.98      ( ~ r2_hidden(X0,X1)
% 0.85/0.98      | ~ r2_hidden(X2,X1)
% 0.85/0.98      | ~ v2_funct_1(X3)
% 0.85/0.98      | X0 = X2
% 0.85/0.98      | k1_funct_1(X3,X0) != k1_funct_1(X3,X2)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | sK3 != k1_xboole_0
% 0.85/0.98      | sK4 != X3
% 0.85/0.98      | k1_xboole_0 != X1 ),
% 0.85/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_244]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_479,plain,
% 0.85/0.98      ( ~ r2_hidden(X0,k1_xboole_0)
% 0.85/0.98      | ~ r2_hidden(X1,k1_xboole_0)
% 0.85/0.98      | ~ v2_funct_1(sK4)
% 0.85/0.98      | X1 = X0
% 0.85/0.98      | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | sK3 != k1_xboole_0 ),
% 0.85/0.98      inference(unflattening,[status(thm)],[c_478]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_483,plain,
% 0.85/0.98      ( ~ r2_hidden(X1,k1_xboole_0)
% 0.85/0.98      | ~ r2_hidden(X0,k1_xboole_0)
% 0.85/0.98      | X1 = X0
% 0.85/0.98      | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | sK3 != k1_xboole_0 ),
% 0.85/0.98      inference(global_propositional_subsumption,
% 0.85/0.98                [status(thm)],
% 0.85/0.98                [c_479,c_12]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_484,plain,
% 0.85/0.98      ( ~ r2_hidden(X0,k1_xboole_0)
% 0.85/0.98      | ~ r2_hidden(X1,k1_xboole_0)
% 0.85/0.98      | X1 = X0
% 0.85/0.98      | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | sK3 != k1_xboole_0 ),
% 0.85/0.98      inference(renaming,[status(thm)],[c_483]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_591,plain,
% 0.85/0.98      ( ~ r2_hidden(X0_45,k1_xboole_0)
% 0.85/0.98      | ~ r2_hidden(X1_45,k1_xboole_0)
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | sK3 != k1_xboole_0
% 0.85/0.98      | X1_45 = X0_45
% 0.85/0.98      | k1_funct_1(sK4,X1_45) != k1_funct_1(sK4,X0_45) ),
% 0.85/0.98      inference(subtyping,[status(esa)],[c_484]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_597,plain,
% 0.85/0.98      ( sP0_iProver_split
% 0.85/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | sK3 != k1_xboole_0 ),
% 0.85/0.98      inference(splitting,
% 0.85/0.98                [splitting(split),new_symbols(definition,[])],
% 0.85/0.98                [c_591]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_720,plain,
% 0.85/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | sK3 != k1_xboole_0
% 0.85/0.98      | sP0_iProver_split = iProver_top ),
% 0.85/0.98      inference(predicate_to_equality,[status(thm)],[c_597]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_621,plain,
% 0.85/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | sK3 != k1_xboole_0
% 0.85/0.98      | sP0_iProver_split = iProver_top ),
% 0.85/0.98      inference(predicate_to_equality,[status(thm)],[c_597]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_812,plain,
% 0.85/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 0.85/0.98      | sP0_iProver_split = iProver_top ),
% 0.85/0.98      inference(global_propositional_subsumption,
% 0.85/0.98                [status(thm)],
% 0.85/0.98                [c_720,c_11,c_10,c_595,c_594,c_621,c_777]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_926,plain,
% 0.85/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 0.85/0.98      | sP0_iProver_split = iProver_top ),
% 0.85/0.98      inference(demodulation,[status(thm)],[c_923,c_812]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_933,plain,
% 0.85/0.98      ( sP0_iProver_split = iProver_top ),
% 0.85/0.98      inference(equality_resolution_simp,[status(thm)],[c_926]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_593,negated_conjecture,
% 0.85/0.98      ( r2_hidden(sK6,sK3) ),
% 0.85/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_718,plain,
% 0.85/0.98      ( r2_hidden(sK6,sK3) = iProver_top ),
% 0.85/0.98      inference(predicate_to_equality,[status(thm)],[c_593]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_928,plain,
% 0.85/0.98      ( r2_hidden(sK6,k1_xboole_0) = iProver_top ),
% 0.85/0.98      inference(demodulation,[status(thm)],[c_923,c_718]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_592,negated_conjecture,
% 0.85/0.98      ( r2_hidden(sK5,sK3) ),
% 0.85/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_719,plain,
% 0.85/0.98      ( r2_hidden(sK5,sK3) = iProver_top ),
% 0.85/0.98      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_927,plain,
% 0.85/0.98      ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 0.85/0.98      inference(demodulation,[status(thm)],[c_923,c_719]) ).
% 0.85/0.98  
% 0.85/0.98  cnf(c_596,plain,
% 0.85/0.98      ( ~ r2_hidden(X0_45,k1_xboole_0)
% 0.85/0.98      | ~ r2_hidden(X1_45,k1_xboole_0)
% 0.85/0.98      | X1_45 = X0_45
% 0.85/0.98      | k1_funct_1(sK4,X1_45) != k1_funct_1(sK4,X0_45)
% 0.85/0.98      | ~ sP0_iProver_split ),
% 0.85/0.98      inference(splitting,
% 0.85/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 0.85/0.99                [c_591]) ).
% 0.85/0.99  
% 0.85/0.99  cnf(c_721,plain,
% 0.85/0.99      ( X0_45 = X1_45
% 0.85/0.99      | k1_funct_1(sK4,X0_45) != k1_funct_1(sK4,X1_45)
% 0.85/0.99      | r2_hidden(X0_45,k1_xboole_0) != iProver_top
% 0.85/0.99      | r2_hidden(X1_45,k1_xboole_0) != iProver_top
% 0.85/0.99      | sP0_iProver_split != iProver_top ),
% 0.85/0.99      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 0.85/0.99  
% 0.85/0.99  cnf(c_824,plain,
% 0.85/0.99      ( k1_funct_1(sK4,X0_45) != k1_funct_1(sK4,sK5)
% 0.85/0.99      | sK6 = X0_45
% 0.85/0.99      | r2_hidden(X0_45,k1_xboole_0) != iProver_top
% 0.85/0.99      | r2_hidden(sK6,k1_xboole_0) != iProver_top
% 0.85/0.99      | sP0_iProver_split != iProver_top ),
% 0.85/0.99      inference(superposition,[status(thm)],[c_594,c_721]) ).
% 0.85/0.99  
% 0.85/0.99  cnf(c_872,plain,
% 0.85/0.99      ( sK6 = sK5
% 0.85/0.99      | r2_hidden(sK6,k1_xboole_0) != iProver_top
% 0.85/0.99      | r2_hidden(sK5,k1_xboole_0) != iProver_top
% 0.85/0.99      | sP0_iProver_split != iProver_top ),
% 0.85/0.99      inference(equality_resolution,[status(thm)],[c_824]) ).
% 0.85/0.99  
% 0.85/0.99  cnf(c_603,plain,
% 0.85/0.99      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 0.85/0.99      theory(equality) ).
% 0.85/0.99  
% 0.85/0.99  cnf(c_782,plain,
% 0.85/0.99      ( sK6 != X0_45 | sK5 != X0_45 | sK5 = sK6 ),
% 0.85/0.99      inference(instantiation,[status(thm)],[c_603]) ).
% 0.85/0.99  
% 0.85/0.99  cnf(c_783,plain,
% 0.85/0.99      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 0.85/0.99      inference(instantiation,[status(thm)],[c_782]) ).
% 0.85/0.99  
% 0.85/0.99  cnf(c_599,plain,( X0_45 = X0_45 ),theory(equality) ).
% 0.85/0.99  
% 0.85/0.99  cnf(c_615,plain,
% 0.85/0.99      ( sK5 = sK5 ),
% 0.85/0.99      inference(instantiation,[status(thm)],[c_599]) ).
% 0.85/0.99  
% 0.85/0.99  cnf(contradiction,plain,
% 0.85/0.99      ( $false ),
% 0.85/0.99      inference(minisat,
% 0.85/0.99                [status(thm)],
% 0.85/0.99                [c_933,c_928,c_927,c_872,c_783,c_595,c_615]) ).
% 0.85/0.99  
% 0.85/0.99  
% 0.85/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 0.85/0.99  
% 0.85/0.99  ------                               Statistics
% 0.85/0.99  
% 0.85/0.99  ------ General
% 0.85/0.99  
% 0.85/0.99  abstr_ref_over_cycles:                  0
% 0.85/0.99  abstr_ref_under_cycles:                 0
% 0.85/0.99  gc_basic_clause_elim:                   0
% 0.85/0.99  forced_gc_time:                         0
% 0.85/0.99  parsing_time:                           0.007
% 0.85/0.99  unif_index_cands_time:                  0.
% 0.85/0.99  unif_index_add_time:                    0.
% 0.85/0.99  orderings_time:                         0.
% 0.85/0.99  out_proof_time:                         0.011
% 0.85/0.99  total_time:                             0.056
% 0.85/0.99  num_of_symbols:                         54
% 0.85/0.99  num_of_terms:                           976
% 0.85/0.99  
% 0.85/0.99  ------ Preprocessing
% 0.85/0.99  
% 0.85/0.99  num_of_splits:                          1
% 0.85/0.99  num_of_split_atoms:                     1
% 0.85/0.99  num_of_reused_defs:                     0
% 0.85/0.99  num_eq_ax_congr_red:                    8
% 0.85/0.99  num_of_sem_filtered_clauses:            1
% 0.85/0.99  num_of_subtypes:                        5
% 0.85/0.99  monotx_restored_types:                  0
% 0.85/0.99  sat_num_of_epr_types:                   0
% 0.85/0.99  sat_num_of_non_cyclic_types:            0
% 0.85/0.99  sat_guarded_non_collapsed_types:        1
% 0.85/0.99  num_pure_diseq_elim:                    0
% 0.85/0.99  simp_replaced_by:                       0
% 0.85/0.99  res_preprocessed:                       62
% 0.85/0.99  prep_upred:                             0
% 0.85/0.99  prep_unflattend:                        33
% 0.85/0.99  smt_new_axioms:                         0
% 0.85/0.99  pred_elim_cands:                        1
% 0.85/0.99  pred_elim:                              5
% 0.85/0.99  pred_elim_cl:                           9
% 0.85/0.99  pred_elim_cycles:                       8
% 0.85/0.99  merged_defs:                            0
% 0.85/0.99  merged_defs_ncl:                        0
% 0.85/0.99  bin_hyper_res:                          0
% 0.85/0.99  prep_cycles:                            4
% 0.85/0.99  pred_elim_time:                         0.005
% 0.85/0.99  splitting_time:                         0.
% 0.85/0.99  sem_filter_time:                        0.
% 0.85/0.99  monotx_time:                            0.
% 0.85/0.99  subtype_inf_time:                       0.
% 0.85/0.99  
% 0.85/0.99  ------ Problem properties
% 0.85/0.99  
% 0.85/0.99  clauses:                                8
% 0.85/0.99  conjectures:                            4
% 0.85/0.99  epr:                                    3
% 0.85/0.99  horn:                                   6
% 0.85/0.99  ground:                                 5
% 0.85/0.99  unary:                                  4
% 0.85/0.99  binary:                                 0
% 0.85/0.99  lits:                                   20
% 0.85/0.99  lits_eq:                                11
% 0.85/0.99  fd_pure:                                0
% 0.85/0.99  fd_pseudo:                              0
% 0.85/0.99  fd_cond:                                0
% 0.85/0.99  fd_pseudo_cond:                         2
% 0.85/0.99  ac_symbols:                             0
% 0.85/0.99  
% 0.85/0.99  ------ Propositional Solver
% 0.85/0.99  
% 0.85/0.99  prop_solver_calls:                      26
% 0.85/0.99  prop_fast_solver_calls:                 425
% 0.85/0.99  smt_solver_calls:                       0
% 0.85/0.99  smt_fast_solver_calls:                  0
% 0.85/0.99  prop_num_of_clauses:                    211
% 0.85/0.99  prop_preprocess_simplified:             1306
% 0.85/0.99  prop_fo_subsumed:                       12
% 0.85/0.99  prop_solver_time:                       0.
% 0.85/0.99  smt_solver_time:                        0.
% 0.85/0.99  smt_fast_solver_time:                   0.
% 0.85/0.99  prop_fast_solver_time:                  0.
% 0.85/0.99  prop_unsat_core_time:                   0.
% 0.85/0.99  
% 0.85/0.99  ------ QBF
% 0.85/0.99  
% 0.85/0.99  qbf_q_res:                              0
% 0.85/0.99  qbf_num_tautologies:                    0
% 0.85/0.99  qbf_prep_cycles:                        0
% 0.85/0.99  
% 0.85/0.99  ------ BMC1
% 0.85/0.99  
% 0.85/0.99  bmc1_current_bound:                     -1
% 0.85/0.99  bmc1_last_solved_bound:                 -1
% 0.85/0.99  bmc1_unsat_core_size:                   -1
% 0.85/0.99  bmc1_unsat_core_parents_size:           -1
% 0.85/0.99  bmc1_merge_next_fun:                    0
% 0.85/0.99  bmc1_unsat_core_clauses_time:           0.
% 0.85/0.99  
% 0.85/0.99  ------ Instantiation
% 0.85/0.99  
% 0.85/0.99  inst_num_of_clauses:                    48
% 0.85/0.99  inst_num_in_passive:                    0
% 0.85/0.99  inst_num_in_active:                     41
% 0.85/0.99  inst_num_in_unprocessed:                7
% 0.85/0.99  inst_num_of_loops:                      50
% 0.85/0.99  inst_num_of_learning_restarts:          0
% 0.85/0.99  inst_num_moves_active_passive:          6
% 0.85/0.99  inst_lit_activity:                      0
% 0.85/0.99  inst_lit_activity_moves:                0
% 0.85/0.99  inst_num_tautologies:                   0
% 0.85/0.99  inst_num_prop_implied:                  0
% 0.85/0.99  inst_num_existing_simplified:           0
% 0.85/0.99  inst_num_eq_res_simplified:             0
% 0.85/0.99  inst_num_child_elim:                    0
% 0.85/0.99  inst_num_of_dismatching_blockings:      5
% 0.85/0.99  inst_num_of_non_proper_insts:           36
% 0.85/0.99  inst_num_of_duplicates:                 0
% 0.85/0.99  inst_inst_num_from_inst_to_res:         0
% 0.85/0.99  inst_dismatching_checking_time:         0.
% 0.85/0.99  
% 0.85/0.99  ------ Resolution
% 0.85/0.99  
% 0.85/0.99  res_num_of_clauses:                     0
% 0.85/0.99  res_num_in_passive:                     0
% 0.85/0.99  res_num_in_active:                      0
% 0.85/0.99  res_num_of_loops:                       66
% 0.85/0.99  res_forward_subset_subsumed:            12
% 0.85/0.99  res_backward_subset_subsumed:           0
% 0.85/0.99  res_forward_subsumed:                   0
% 0.85/0.99  res_backward_subsumed:                  0
% 0.85/0.99  res_forward_subsumption_resolution:     0
% 0.85/0.99  res_backward_subsumption_resolution:    0
% 0.85/0.99  res_clause_to_clause_subsumption:       16
% 0.85/0.99  res_orphan_elimination:                 0
% 0.85/0.99  res_tautology_del:                      6
% 0.85/0.99  res_num_eq_res_simplified:              1
% 0.85/0.99  res_num_sel_changes:                    0
% 0.85/0.99  res_moves_from_active_to_pass:          0
% 0.85/0.99  
% 0.85/0.99  ------ Superposition
% 0.85/0.99  
% 0.85/0.99  sup_time_total:                         0.
% 0.85/0.99  sup_time_generating:                    0.
% 0.85/0.99  sup_time_sim_full:                      0.
% 0.85/0.99  sup_time_sim_immed:                     0.
% 0.85/0.99  
% 0.85/0.99  sup_num_of_clauses:                     10
% 0.85/0.99  sup_num_in_active:                      5
% 0.85/0.99  sup_num_in_passive:                     5
% 0.85/0.99  sup_num_of_loops:                       8
% 0.85/0.99  sup_fw_superposition:                   3
% 0.85/0.99  sup_bw_superposition:                   0
% 0.85/0.99  sup_immediate_simplified:               0
% 0.85/0.99  sup_given_eliminated:                   0
% 0.85/0.99  comparisons_done:                       0
% 0.85/0.99  comparisons_avoided:                    0
% 0.85/0.99  
% 0.85/0.99  ------ Simplifications
% 0.85/0.99  
% 0.85/0.99  
% 0.85/0.99  sim_fw_subset_subsumed:                 0
% 0.85/0.99  sim_bw_subset_subsumed:                 0
% 0.85/0.99  sim_fw_subsumed:                        0
% 0.85/0.99  sim_bw_subsumed:                        0
% 0.85/0.99  sim_fw_subsumption_res:                 0
% 0.85/0.99  sim_bw_subsumption_res:                 0
% 0.85/0.99  sim_tautology_del:                      0
% 0.85/0.99  sim_eq_tautology_del:                   2
% 0.85/0.99  sim_eq_res_simp:                        1
% 0.85/0.99  sim_fw_demodulated:                     0
% 0.85/0.99  sim_bw_demodulated:                     3
% 0.85/0.99  sim_light_normalised:                   0
% 0.85/0.99  sim_joinable_taut:                      0
% 0.85/0.99  sim_joinable_simp:                      0
% 0.85/0.99  sim_ac_normalised:                      0
% 0.85/0.99  sim_smt_subsumption:                    0
% 0.85/0.99  
%------------------------------------------------------------------------------
