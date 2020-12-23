%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:57 EST 2020

% Result     : Theorem 1.11s
% Output     : CNFRefutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :  160 (14803 expanded)
%              Number of clauses        :  125 (3664 expanded)
%              Number of leaves         :   10 (3183 expanded)
%              Depth                    :   36
%              Number of atoms          :  691 (128725 expanded)
%              Number of equality atoms :  385 (43436 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,plain,(
    ! [X2,X0] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      | ~ sP0(X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f12,plain,(
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

fof(f13,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f11,f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK1(X0,X1)) = k1_funct_1(X0,sK2(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,conjecture,(
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

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f15])).

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
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK4,X2) = k1_funct_1(sK4,X3)
            & r2_hidden(X3,sK3)
            & r2_hidden(X2,sK3) )
        | ~ v2_funct_1(sK4) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5)
            | ~ r2_hidden(X5,sK3)
            | ~ r2_hidden(X4,sK3) )
        | v2_funct_1(sK4) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
      & v1_funct_2(sK4,sK3,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ( ( sK5 != sK6
        & k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
        & r2_hidden(sK6,sK3)
        & r2_hidden(sK5,sK3) )
      | ~ v2_funct_1(sK4) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5)
          | ~ r2_hidden(X5,sK3)
          | ~ r2_hidden(X4,sK3) )
      | v2_funct_1(sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    & v1_funct_2(sK4,sK3,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f16,f18,f17])).

fof(f28,plain,(
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

fof(f4,plain,(
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
    inference(flattening,[],[f4])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( sP0(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f5,f8])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X2,X1] :
      ( sP0(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f26])).

fof(f29,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,
    ( r2_hidden(sK5,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,
    ( r2_hidden(sK6,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,
    ( sK5 != sK6
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | k1_funct_1(X0,X4) != k1_funct_1(X0,X5)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ v2_funct_1(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5)
      | ~ r2_hidden(X5,sK3)
      | ~ r2_hidden(X4,sK3)
      | v2_funct_1(sK4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | sK1(X0,X1) != sK2(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_1,plain,
    ( ~ sP0(X0,X1)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK2(X0,X1)) = k1_funct_1(X0,sK1(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_13,negated_conjecture,
    ( v1_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | sP0(X0,k1_xboole_0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_167,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | sP0(X0,k1_xboole_0)
    | ~ v1_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_12])).

cnf(c_168,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
    | sP0(sK4,k1_xboole_0)
    | ~ v1_funct_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
    inference(unflattening,[status(thm)],[c_167])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_172,plain,
    ( sP0(sK4,k1_xboole_0)
    | ~ v1_funct_2(sK4,k1_xboole_0,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_168,c_14])).

cnf(c_173,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
    | sP0(sK4,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
    inference(renaming,[status(thm)],[c_172])).

cnf(c_221,plain,
    ( sP0(sK4,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != X0
    | sK3 != k1_xboole_0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_173])).

cnf(c_222,plain,
    ( sP0(sK4,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_287,plain,
    ( v2_funct_1(X0)
    | k1_funct_1(X0,sK2(X0,X1)) = k1_funct_1(X0,sK1(X0,X1))
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0
    | sK4 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_222])).

cnf(c_288,plain,
    ( v2_funct_1(sK4)
    | k1_funct_1(sK4,sK2(sK4,k1_xboole_0)) = k1_funct_1(sK4,sK1(sK4,k1_xboole_0))
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_1291,plain,
    ( v2_funct_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | k1_funct_1(sK4,sK2(sK4,k1_xboole_0)) = k1_funct_1(sK4,sK1(sK4,k1_xboole_0))
    | sK3 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_288])).

cnf(c_1581,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | k1_funct_1(sK4,sK2(sK4,k1_xboole_0)) = k1_funct_1(sK4,sK1(sK4,k1_xboole_0))
    | sK3 != k1_xboole_0
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1291])).

cnf(c_1303,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_1325,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1303])).

cnf(c_1336,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | k1_funct_1(sK4,sK2(sK4,k1_xboole_0)) = k1_funct_1(sK4,sK1(sK4,k1_xboole_0))
    | sK3 != k1_xboole_0
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1291])).

cnf(c_1316,plain,
    ( X0_49 != X1_49
    | k1_zfmisc_1(X0_49) = k1_zfmisc_1(X1_49) ),
    theory(equality)).

cnf(c_1777,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) != k2_zfmisc_1(sK3,sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_1316])).

cnf(c_1315,plain,
    ( k2_zfmisc_1(X0_45,X1_45) = k2_zfmisc_1(X2_45,X3_45)
    | X0_45 != X2_45
    | X1_45 != X3_45 ),
    theory(equality)).

cnf(c_1783,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(sK3,sK3)
    | sK3 != sK3
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1315])).

cnf(c_1308,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_1808,plain,
    ( sK3 != X0_45
    | k1_xboole_0 != X0_45
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1308])).

cnf(c_1847,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1808])).

cnf(c_1848,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1303])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sP0(X0,X1)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_188,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | sP0(X0,X1)
    | ~ v1_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_189,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | sP0(sK4,X0)
    | ~ v1_funct_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_193,plain,
    ( sP0(sK4,X0)
    | ~ v1_funct_2(sK4,X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_189,c_14])).

cnf(c_194,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | sP0(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_193])).

cnf(c_234,plain,
    ( sP0(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != X0
    | sK3 != X1
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_194])).

cnf(c_235,plain,
    ( sP0(sK4,sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_345,plain,
    ( v2_funct_1(X0)
    | k1_funct_1(X0,sK2(X0,X1)) = k1_funct_1(X0,sK1(X0,X1))
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != X1
    | sK3 = k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_235])).

cnf(c_346,plain,
    ( v2_funct_1(sK4)
    | k1_funct_1(sK4,sK2(sK4,sK3)) = k1_funct_1(sK4,sK1(sK4,sK3))
    | sK3 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_1287,plain,
    ( v2_funct_1(sK4)
    | k1_funct_1(sK4,sK2(sK4,sK3)) = k1_funct_1(sK4,sK1(sK4,sK3))
    | sK3 = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_346])).

cnf(c_1585,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK3)) = k1_funct_1(sK4,sK1(sK4,sK3))
    | sK3 = k1_xboole_0
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1287])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK5,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_21,plain,
    ( r2_hidden(sK5,sK3) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(sK6,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_22,plain,
    ( r2_hidden(sK6,sK3) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | sK5 != sK6 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1298,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | sK5 != sK6 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1329,plain,
    ( sK5 != sK6
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1298])).

cnf(c_8,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1297,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1330,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1297])).

cnf(c_1340,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK3)) = k1_funct_1(sK4,sK1(sK4,sK3))
    | sK3 = k1_xboole_0
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1287])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ sP0(X3,X1)
    | ~ v2_funct_1(X3)
    | X0 = X2
    | k1_funct_1(X3,X0) != k1_funct_1(X3,X2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_398,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ v2_funct_1(X3)
    | X0 = X2
    | k1_funct_1(X3,X0) != k1_funct_1(X3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != X1
    | sK3 = k1_xboole_0
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_235])).

cnf(c_399,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X1,sK3)
    | ~ v2_funct_1(sK4)
    | X1 = X0
    | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0)
    | sK3 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X1,sK3)
    | v2_funct_1(sK4)
    | X1 = X0
    | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_403,plain,
    ( ~ r2_hidden(X1,sK3)
    | ~ r2_hidden(X0,sK3)
    | X1 = X0
    | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_399,c_11])).

cnf(c_404,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X1,sK3)
    | X1 = X0
    | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0)
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_403])).

cnf(c_1284,plain,
    ( ~ r2_hidden(X0_44,sK3)
    | ~ r2_hidden(X1_44,sK3)
    | k1_funct_1(sK4,X1_44) != k1_funct_1(sK4,X0_44)
    | sK3 = k1_xboole_0
    | X1_44 = X0_44 ),
    inference(subtyping,[status(esa)],[c_404])).

cnf(c_1739,plain,
    ( ~ r2_hidden(sK6,sK3)
    | ~ r2_hidden(sK5,sK3)
    | k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
    | sK3 = k1_xboole_0
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_1284])).

cnf(c_1740,plain,
    ( k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
    | sK3 = k1_xboole_0
    | sK5 = sK6
    | r2_hidden(sK6,sK3) != iProver_top
    | r2_hidden(sK5,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1739])).

cnf(c_1870,plain,
    ( sK3 = k1_xboole_0
    | k1_funct_1(sK4,sK2(sK4,sK3)) = k1_funct_1(sK4,sK1(sK4,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1585,c_21,c_22,c_1329,c_1330,c_1340,c_1740])).

cnf(c_1871,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK3)) = k1_funct_1(sK4,sK1(sK4,sK3))
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1870])).

cnf(c_1294,negated_conjecture,
    ( ~ r2_hidden(X0_44,sK3)
    | ~ r2_hidden(X1_44,sK3)
    | v2_funct_1(sK4)
    | k1_funct_1(sK4,X1_44) != k1_funct_1(sK4,X0_44)
    | X1_44 = X0_44 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1578,plain,
    ( k1_funct_1(sK4,X0_44) != k1_funct_1(sK4,X1_44)
    | X0_44 = X1_44
    | r2_hidden(X0_44,sK3) != iProver_top
    | r2_hidden(X1_44,sK3) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1294])).

cnf(c_1874,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK3)) != k1_funct_1(sK4,X0_44)
    | sK3 = k1_xboole_0
    | sK2(sK4,sK3) = X0_44
    | r2_hidden(X0_44,sK3) != iProver_top
    | r2_hidden(sK2(sK4,sK3),sK3) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1871,c_1578])).

cnf(c_2,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | ~ sP0(X0,X1)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_332,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | v2_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != X1
    | sK3 = k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_235])).

cnf(c_333,plain,
    ( r2_hidden(sK2(sK4,sK3),sK3)
    | v2_funct_1(sK4)
    | sK3 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_1288,plain,
    ( r2_hidden(sK2(sK4,sK3),sK3)
    | v2_funct_1(sK4)
    | sK3 = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_333])).

cnf(c_1584,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK2(sK4,sK3),sK3) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1288])).

cnf(c_1339,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK2(sK4,sK3),sK3) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1288])).

cnf(c_1830,plain,
    ( r2_hidden(sK2(sK4,sK3),sK3) = iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1584,c_21,c_22,c_1329,c_1330,c_1339,c_1740])).

cnf(c_1831,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK2(sK4,sK3),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_1830])).

cnf(c_1911,plain,
    ( k1_funct_1(sK4,sK1(sK4,sK3)) != k1_funct_1(sK4,X0_44)
    | sK3 = k1_xboole_0
    | sK2(sK4,sK3) = X0_44
    | r2_hidden(X0_44,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1874,c_21,c_22,c_1329,c_1330,c_1339,c_1740])).

cnf(c_1922,plain,
    ( sK3 = k1_xboole_0
    | sK2(sK4,sK3) = sK1(sK4,sK3)
    | r2_hidden(sK1(sK4,sK3),sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1911])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | ~ sP0(X0,X1)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_319,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | v2_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != X1
    | sK3 = k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_235])).

cnf(c_320,plain,
    ( r2_hidden(sK1(sK4,sK3),sK3)
    | v2_funct_1(sK4)
    | sK3 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_1289,plain,
    ( r2_hidden(sK1(sK4,sK3),sK3)
    | v2_funct_1(sK4)
    | sK3 = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_320])).

cnf(c_1583,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK3),sK3) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1289])).

cnf(c_1338,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK3),sK3) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1289])).

cnf(c_1823,plain,
    ( r2_hidden(sK1(sK4,sK3),sK3) = iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1583,c_21,c_22,c_1329,c_1330,c_1338,c_1740])).

cnf(c_1824,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4,sK3),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_1823])).

cnf(c_0,plain,
    ( ~ sP0(X0,X1)
    | v2_funct_1(X0)
    | sK2(X0,X1) != sK1(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_358,plain,
    ( v2_funct_1(X0)
    | sK2(X0,X1) != sK1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != X1
    | sK3 = k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_235])).

cnf(c_359,plain,
    ( v2_funct_1(sK4)
    | sK2(sK4,sK3) != sK1(sK4,sK3)
    | sK3 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_1286,plain,
    ( v2_funct_1(sK4)
    | sK3 = k1_xboole_0
    | sK2(sK4,sK3) != sK1(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_359])).

cnf(c_1586,plain,
    ( sK3 = k1_xboole_0
    | sK2(sK4,sK3) != sK1(sK4,sK3)
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1286])).

cnf(c_1341,plain,
    ( sK3 = k1_xboole_0
    | sK2(sK4,sK3) != sK1(sK4,sK3)
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1286])).

cnf(c_1865,plain,
    ( sK2(sK4,sK3) != sK1(sK4,sK3)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1586,c_21,c_22,c_1329,c_1330,c_1341,c_1740])).

cnf(c_1866,plain,
    ( sK3 = k1_xboole_0
    | sK2(sK4,sK3) != sK1(sK4,sK3) ),
    inference(renaming,[status(thm)],[c_1865])).

cnf(c_2001,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1922,c_1824,c_1866])).

cnf(c_1295,negated_conjecture,
    ( r2_hidden(sK5,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1577,plain,
    ( r2_hidden(sK5,sK3) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1295])).

cnf(c_2010,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2001,c_1577])).

cnf(c_371,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ v2_funct_1(X3)
    | X0 = X2
    | k1_funct_1(X3,X0) != k1_funct_1(X3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0
    | sK4 != X3
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_222])).

cnf(c_372,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0)
    | ~ v2_funct_1(sK4)
    | X1 = X0
    | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_1285,plain,
    ( ~ r2_hidden(X0_44,k1_xboole_0)
    | ~ r2_hidden(X1_44,k1_xboole_0)
    | ~ v2_funct_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | k1_funct_1(sK4,X1_44) != k1_funct_1(sK4,X0_44)
    | sK3 != k1_xboole_0
    | X1_44 = X0_44 ),
    inference(subtyping,[status(esa)],[c_372])).

cnf(c_1300,plain,
    ( ~ v2_funct_1(sK4)
    | sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1285])).

cnf(c_1342,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0
    | v2_funct_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1300])).

cnf(c_1299,plain,
    ( ~ r2_hidden(X0_44,k1_xboole_0)
    | ~ r2_hidden(X1_44,k1_xboole_0)
    | k1_funct_1(sK4,X1_44) != k1_funct_1(sK4,X0_44)
    | X1_44 = X0_44
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1285])).

cnf(c_1879,plain,
    ( ~ r2_hidden(sK6,k1_xboole_0)
    | ~ r2_hidden(sK5,k1_xboole_0)
    | ~ sP0_iProver_split
    | k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_1299])).

cnf(c_1880,plain,
    ( k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
    | sK5 = sK6
    | r2_hidden(sK6,k1_xboole_0) != iProver_top
    | r2_hidden(sK5,k1_xboole_0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1879])).

cnf(c_1296,negated_conjecture,
    ( r2_hidden(sK6,sK3)
    | ~ v2_funct_1(sK4) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1576,plain,
    ( r2_hidden(sK6,sK3) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1296])).

cnf(c_2011,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2001,c_1576])).

cnf(c_2052,plain,
    ( v2_funct_1(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2010,c_1325,c_1329,c_1330,c_1342,c_1777,c_1783,c_1824,c_1847,c_1848,c_1866,c_1880,c_1922,c_2011])).

cnf(c_2214,plain,
    ( k1_funct_1(sK4,sK2(sK4,k1_xboole_0)) = k1_funct_1(sK4,sK1(sK4,k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1581,c_1325,c_1329,c_1330,c_1336,c_1342,c_1777,c_1783,c_1824,c_1847,c_1848,c_1866,c_1880,c_1922,c_2010,c_2011])).

cnf(c_2009,plain,
    ( k1_funct_1(sK4,X0_44) != k1_funct_1(sK4,X1_44)
    | X1_44 = X0_44
    | r2_hidden(X1_44,k1_xboole_0) != iProver_top
    | r2_hidden(X0_44,k1_xboole_0) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2001,c_1578])).

cnf(c_2113,plain,
    ( r2_hidden(X0_44,k1_xboole_0) != iProver_top
    | r2_hidden(X1_44,k1_xboole_0) != iProver_top
    | X1_44 = X0_44
    | k1_funct_1(sK4,X0_44) != k1_funct_1(sK4,X1_44) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2009,c_1325,c_1329,c_1330,c_1342,c_1777,c_1783,c_1824,c_1847,c_1848,c_1866,c_1880,c_1922,c_2010,c_2011])).

cnf(c_2114,plain,
    ( k1_funct_1(sK4,X0_44) != k1_funct_1(sK4,X1_44)
    | X1_44 = X0_44
    | r2_hidden(X1_44,k1_xboole_0) != iProver_top
    | r2_hidden(X0_44,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2113])).

cnf(c_2219,plain,
    ( k1_funct_1(sK4,sK1(sK4,k1_xboole_0)) != k1_funct_1(sK4,X0_44)
    | sK2(sK4,k1_xboole_0) = X0_44
    | r2_hidden(X0_44,k1_xboole_0) != iProver_top
    | r2_hidden(sK2(sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2214,c_2114])).

cnf(c_271,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | v2_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0
    | sK4 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_222])).

cnf(c_272,plain,
    ( r2_hidden(sK2(sK4,k1_xboole_0),k1_xboole_0)
    | v2_funct_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_1292,plain,
    ( r2_hidden(sK2(sK4,k1_xboole_0),k1_xboole_0)
    | v2_funct_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_272])).

cnf(c_1335,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0
    | r2_hidden(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1292])).

cnf(c_2279,plain,
    ( r2_hidden(X0_44,k1_xboole_0) != iProver_top
    | sK2(sK4,k1_xboole_0) = X0_44
    | k1_funct_1(sK4,sK1(sK4,k1_xboole_0)) != k1_funct_1(sK4,X0_44) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2219,c_1325,c_1329,c_1330,c_1335,c_1342,c_1777,c_1783,c_1824,c_1847,c_1848,c_1866,c_1880,c_1922,c_2010,c_2011])).

cnf(c_2280,plain,
    ( k1_funct_1(sK4,sK1(sK4,k1_xboole_0)) != k1_funct_1(sK4,X0_44)
    | sK2(sK4,k1_xboole_0) = X0_44
    | r2_hidden(X0_44,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2279])).

cnf(c_2289,plain,
    ( sK2(sK4,k1_xboole_0) = sK1(sK4,k1_xboole_0)
    | r2_hidden(sK1(sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2280])).

cnf(c_303,plain,
    ( v2_funct_1(X0)
    | sK2(X0,X1) != sK1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0
    | sK4 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_222])).

cnf(c_304,plain,
    ( v2_funct_1(sK4)
    | sK2(sK4,k1_xboole_0) != sK1(sK4,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_1290,plain,
    ( v2_funct_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0
    | sK2(sK4,k1_xboole_0) != sK1(sK4,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_304])).

cnf(c_1337,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0
    | sK2(sK4,k1_xboole_0) != sK1(sK4,k1_xboole_0)
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1290])).

cnf(c_255,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | v2_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0
    | sK4 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_222])).

cnf(c_256,plain,
    ( r2_hidden(sK1(sK4,k1_xboole_0),k1_xboole_0)
    | v2_funct_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_255])).

cnf(c_1293,plain,
    ( r2_hidden(sK1(sK4,k1_xboole_0),k1_xboole_0)
    | v2_funct_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_256])).

cnf(c_1334,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK3 != k1_xboole_0
    | r2_hidden(sK1(sK4,k1_xboole_0),k1_xboole_0) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1293])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2289,c_2052,c_2001,c_1848,c_1847,c_1783,c_1777,c_1337,c_1334,c_1325])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:30:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.11/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.11/0.98  
% 1.11/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.11/0.98  
% 1.11/0.98  ------  iProver source info
% 1.11/0.98  
% 1.11/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.11/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.11/0.98  git: non_committed_changes: false
% 1.11/0.98  git: last_make_outside_of_git: false
% 1.11/0.98  
% 1.11/0.98  ------ 
% 1.11/0.98  
% 1.11/0.98  ------ Input Options
% 1.11/0.98  
% 1.11/0.98  --out_options                           all
% 1.11/0.98  --tptp_safe_out                         true
% 1.11/0.98  --problem_path                          ""
% 1.11/0.98  --include_path                          ""
% 1.11/0.98  --clausifier                            res/vclausify_rel
% 1.11/0.98  --clausifier_options                    --mode clausify
% 1.11/0.98  --stdin                                 false
% 1.11/0.98  --stats_out                             all
% 1.11/0.98  
% 1.11/0.98  ------ General Options
% 1.11/0.98  
% 1.11/0.98  --fof                                   false
% 1.11/0.98  --time_out_real                         305.
% 1.11/0.98  --time_out_virtual                      -1.
% 1.11/0.98  --symbol_type_check                     false
% 1.11/0.98  --clausify_out                          false
% 1.11/0.98  --sig_cnt_out                           false
% 1.11/0.98  --trig_cnt_out                          false
% 1.11/0.98  --trig_cnt_out_tolerance                1.
% 1.11/0.98  --trig_cnt_out_sk_spl                   false
% 1.11/0.98  --abstr_cl_out                          false
% 1.11/0.98  
% 1.11/0.98  ------ Global Options
% 1.11/0.98  
% 1.11/0.98  --schedule                              default
% 1.11/0.98  --add_important_lit                     false
% 1.11/0.98  --prop_solver_per_cl                    1000
% 1.11/0.98  --min_unsat_core                        false
% 1.11/0.98  --soft_assumptions                      false
% 1.11/0.98  --soft_lemma_size                       3
% 1.11/0.98  --prop_impl_unit_size                   0
% 1.11/0.98  --prop_impl_unit                        []
% 1.11/0.98  --share_sel_clauses                     true
% 1.11/0.98  --reset_solvers                         false
% 1.11/0.98  --bc_imp_inh                            [conj_cone]
% 1.11/0.98  --conj_cone_tolerance                   3.
% 1.11/0.98  --extra_neg_conj                        none
% 1.11/0.98  --large_theory_mode                     true
% 1.11/0.98  --prolific_symb_bound                   200
% 1.11/0.98  --lt_threshold                          2000
% 1.11/0.98  --clause_weak_htbl                      true
% 1.11/0.98  --gc_record_bc_elim                     false
% 1.11/0.98  
% 1.11/0.98  ------ Preprocessing Options
% 1.11/0.98  
% 1.11/0.98  --preprocessing_flag                    true
% 1.11/0.98  --time_out_prep_mult                    0.1
% 1.11/0.98  --splitting_mode                        input
% 1.11/0.98  --splitting_grd                         true
% 1.11/0.98  --splitting_cvd                         false
% 1.11/0.98  --splitting_cvd_svl                     false
% 1.11/0.98  --splitting_nvd                         32
% 1.11/0.98  --sub_typing                            true
% 1.11/0.98  --prep_gs_sim                           true
% 1.11/0.98  --prep_unflatten                        true
% 1.11/0.98  --prep_res_sim                          true
% 1.11/0.98  --prep_upred                            true
% 1.11/0.98  --prep_sem_filter                       exhaustive
% 1.11/0.98  --prep_sem_filter_out                   false
% 1.11/0.98  --pred_elim                             true
% 1.11/0.98  --res_sim_input                         true
% 1.11/0.98  --eq_ax_congr_red                       true
% 1.11/0.98  --pure_diseq_elim                       true
% 1.11/0.98  --brand_transform                       false
% 1.11/0.98  --non_eq_to_eq                          false
% 1.11/0.98  --prep_def_merge                        true
% 1.11/0.98  --prep_def_merge_prop_impl              false
% 1.11/0.98  --prep_def_merge_mbd                    true
% 1.11/0.98  --prep_def_merge_tr_red                 false
% 1.11/0.98  --prep_def_merge_tr_cl                  false
% 1.11/0.98  --smt_preprocessing                     true
% 1.11/0.98  --smt_ac_axioms                         fast
% 1.11/0.98  --preprocessed_out                      false
% 1.11/0.98  --preprocessed_stats                    false
% 1.11/0.98  
% 1.11/0.98  ------ Abstraction refinement Options
% 1.11/0.98  
% 1.11/0.98  --abstr_ref                             []
% 1.11/0.98  --abstr_ref_prep                        false
% 1.11/0.98  --abstr_ref_until_sat                   false
% 1.11/0.98  --abstr_ref_sig_restrict                funpre
% 1.11/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.11/0.98  --abstr_ref_under                       []
% 1.11/0.98  
% 1.11/0.98  ------ SAT Options
% 1.11/0.98  
% 1.11/0.98  --sat_mode                              false
% 1.11/0.98  --sat_fm_restart_options                ""
% 1.11/0.98  --sat_gr_def                            false
% 1.11/0.98  --sat_epr_types                         true
% 1.11/0.98  --sat_non_cyclic_types                  false
% 1.11/0.98  --sat_finite_models                     false
% 1.11/0.98  --sat_fm_lemmas                         false
% 1.11/0.98  --sat_fm_prep                           false
% 1.11/0.98  --sat_fm_uc_incr                        true
% 1.11/0.98  --sat_out_model                         small
% 1.11/0.98  --sat_out_clauses                       false
% 1.11/0.98  
% 1.11/0.98  ------ QBF Options
% 1.11/0.98  
% 1.11/0.98  --qbf_mode                              false
% 1.11/0.98  --qbf_elim_univ                         false
% 1.11/0.98  --qbf_dom_inst                          none
% 1.11/0.98  --qbf_dom_pre_inst                      false
% 1.11/0.98  --qbf_sk_in                             false
% 1.11/0.98  --qbf_pred_elim                         true
% 1.11/0.98  --qbf_split                             512
% 1.11/0.98  
% 1.11/0.98  ------ BMC1 Options
% 1.11/0.98  
% 1.11/0.98  --bmc1_incremental                      false
% 1.11/0.98  --bmc1_axioms                           reachable_all
% 1.11/0.98  --bmc1_min_bound                        0
% 1.11/0.98  --bmc1_max_bound                        -1
% 1.11/0.98  --bmc1_max_bound_default                -1
% 1.11/0.98  --bmc1_symbol_reachability              true
% 1.11/0.98  --bmc1_property_lemmas                  false
% 1.11/0.98  --bmc1_k_induction                      false
% 1.11/0.98  --bmc1_non_equiv_states                 false
% 1.11/0.98  --bmc1_deadlock                         false
% 1.11/0.98  --bmc1_ucm                              false
% 1.11/0.98  --bmc1_add_unsat_core                   none
% 1.11/0.98  --bmc1_unsat_core_children              false
% 1.11/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.11/0.98  --bmc1_out_stat                         full
% 1.11/0.98  --bmc1_ground_init                      false
% 1.11/0.98  --bmc1_pre_inst_next_state              false
% 1.11/0.98  --bmc1_pre_inst_state                   false
% 1.11/0.98  --bmc1_pre_inst_reach_state             false
% 1.11/0.98  --bmc1_out_unsat_core                   false
% 1.11/0.98  --bmc1_aig_witness_out                  false
% 1.11/0.98  --bmc1_verbose                          false
% 1.11/0.98  --bmc1_dump_clauses_tptp                false
% 1.11/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.11/0.98  --bmc1_dump_file                        -
% 1.11/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.11/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.11/0.98  --bmc1_ucm_extend_mode                  1
% 1.11/0.98  --bmc1_ucm_init_mode                    2
% 1.11/0.98  --bmc1_ucm_cone_mode                    none
% 1.11/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.11/0.98  --bmc1_ucm_relax_model                  4
% 1.11/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.11/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.11/0.98  --bmc1_ucm_layered_model                none
% 1.11/0.98  --bmc1_ucm_max_lemma_size               10
% 1.11/0.98  
% 1.11/0.98  ------ AIG Options
% 1.11/0.98  
% 1.11/0.98  --aig_mode                              false
% 1.11/0.98  
% 1.11/0.98  ------ Instantiation Options
% 1.11/0.98  
% 1.11/0.98  --instantiation_flag                    true
% 1.11/0.98  --inst_sos_flag                         false
% 1.11/0.98  --inst_sos_phase                        true
% 1.11/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.11/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.11/0.98  --inst_lit_sel_side                     num_symb
% 1.11/0.98  --inst_solver_per_active                1400
% 1.11/0.98  --inst_solver_calls_frac                1.
% 1.11/0.98  --inst_passive_queue_type               priority_queues
% 1.11/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.11/0.98  --inst_passive_queues_freq              [25;2]
% 1.11/0.98  --inst_dismatching                      true
% 1.11/0.98  --inst_eager_unprocessed_to_passive     true
% 1.11/0.98  --inst_prop_sim_given                   true
% 1.11/0.98  --inst_prop_sim_new                     false
% 1.11/0.98  --inst_subs_new                         false
% 1.11/0.98  --inst_eq_res_simp                      false
% 1.11/0.98  --inst_subs_given                       false
% 1.11/0.98  --inst_orphan_elimination               true
% 1.11/0.98  --inst_learning_loop_flag               true
% 1.11/0.98  --inst_learning_start                   3000
% 1.11/0.98  --inst_learning_factor                  2
% 1.11/0.98  --inst_start_prop_sim_after_learn       3
% 1.11/0.98  --inst_sel_renew                        solver
% 1.11/0.98  --inst_lit_activity_flag                true
% 1.11/0.98  --inst_restr_to_given                   false
% 1.11/0.98  --inst_activity_threshold               500
% 1.11/0.98  --inst_out_proof                        true
% 1.11/0.98  
% 1.11/0.98  ------ Resolution Options
% 1.11/0.98  
% 1.11/0.98  --resolution_flag                       true
% 1.11/0.98  --res_lit_sel                           adaptive
% 1.11/0.98  --res_lit_sel_side                      none
% 1.11/0.98  --res_ordering                          kbo
% 1.11/0.98  --res_to_prop_solver                    active
% 1.11/0.98  --res_prop_simpl_new                    false
% 1.11/0.98  --res_prop_simpl_given                  true
% 1.11/0.98  --res_passive_queue_type                priority_queues
% 1.11/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.11/0.98  --res_passive_queues_freq               [15;5]
% 1.11/0.98  --res_forward_subs                      full
% 1.11/0.98  --res_backward_subs                     full
% 1.11/0.98  --res_forward_subs_resolution           true
% 1.11/0.98  --res_backward_subs_resolution          true
% 1.11/0.98  --res_orphan_elimination                true
% 1.11/0.98  --res_time_limit                        2.
% 1.11/0.98  --res_out_proof                         true
% 1.11/0.98  
% 1.11/0.98  ------ Superposition Options
% 1.11/0.98  
% 1.11/0.98  --superposition_flag                    true
% 1.11/0.98  --sup_passive_queue_type                priority_queues
% 1.11/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.11/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.11/0.98  --demod_completeness_check              fast
% 1.11/0.98  --demod_use_ground                      true
% 1.11/0.98  --sup_to_prop_solver                    passive
% 1.11/0.98  --sup_prop_simpl_new                    true
% 1.11/0.98  --sup_prop_simpl_given                  true
% 1.11/0.98  --sup_fun_splitting                     false
% 1.11/0.98  --sup_smt_interval                      50000
% 1.11/0.98  
% 1.11/0.98  ------ Superposition Simplification Setup
% 1.11/0.98  
% 1.11/0.98  --sup_indices_passive                   []
% 1.11/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.11/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/0.98  --sup_full_bw                           [BwDemod]
% 1.11/0.98  --sup_immed_triv                        [TrivRules]
% 1.11/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.11/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/0.98  --sup_immed_bw_main                     []
% 1.11/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.11/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.11/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.11/0.98  
% 1.11/0.98  ------ Combination Options
% 1.11/0.98  
% 1.11/0.98  --comb_res_mult                         3
% 1.11/0.98  --comb_sup_mult                         2
% 1.11/0.98  --comb_inst_mult                        10
% 1.11/0.98  
% 1.11/0.98  ------ Debug Options
% 1.11/0.98  
% 1.11/0.98  --dbg_backtrace                         false
% 1.11/0.98  --dbg_dump_prop_clauses                 false
% 1.11/0.98  --dbg_dump_prop_clauses_file            -
% 1.11/0.98  --dbg_out_stat                          false
% 1.11/0.98  ------ Parsing...
% 1.11/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.11/0.98  
% 1.11/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 1.11/0.98  
% 1.11/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.11/0.98  
% 1.11/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.11/0.98  ------ Proving...
% 1.11/0.98  ------ Problem Properties 
% 1.11/0.98  
% 1.11/0.98  
% 1.11/0.98  clauses                                 16
% 1.11/0.98  conjectures                             5
% 1.11/0.98  EPR                                     3
% 1.11/0.98  Horn                                    7
% 1.11/0.98  unary                                   0
% 1.11/0.98  binary                                  4
% 1.11/0.98  lits                                    55
% 1.11/0.98  lits eq                                 27
% 1.11/0.98  fd_pure                                 0
% 1.11/0.98  fd_pseudo                               0
% 1.11/0.98  fd_cond                                 0
% 1.11/0.98  fd_pseudo_cond                          3
% 1.11/0.98  AC symbols                              0
% 1.11/0.98  
% 1.11/0.98  ------ Schedule dynamic 5 is on 
% 1.11/0.98  
% 1.11/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.11/0.98  
% 1.11/0.98  
% 1.11/0.98  ------ 
% 1.11/0.98  Current options:
% 1.11/0.98  ------ 
% 1.11/0.98  
% 1.11/0.98  ------ Input Options
% 1.11/0.98  
% 1.11/0.98  --out_options                           all
% 1.11/0.98  --tptp_safe_out                         true
% 1.11/0.98  --problem_path                          ""
% 1.11/0.98  --include_path                          ""
% 1.11/0.98  --clausifier                            res/vclausify_rel
% 1.11/0.98  --clausifier_options                    --mode clausify
% 1.11/0.98  --stdin                                 false
% 1.11/0.98  --stats_out                             all
% 1.11/0.98  
% 1.11/0.98  ------ General Options
% 1.11/0.98  
% 1.11/0.98  --fof                                   false
% 1.11/0.98  --time_out_real                         305.
% 1.11/0.98  --time_out_virtual                      -1.
% 1.11/0.98  --symbol_type_check                     false
% 1.11/0.98  --clausify_out                          false
% 1.11/0.98  --sig_cnt_out                           false
% 1.11/0.98  --trig_cnt_out                          false
% 1.11/0.98  --trig_cnt_out_tolerance                1.
% 1.11/0.98  --trig_cnt_out_sk_spl                   false
% 1.11/0.98  --abstr_cl_out                          false
% 1.11/0.98  
% 1.11/0.98  ------ Global Options
% 1.11/0.98  
% 1.11/0.98  --schedule                              default
% 1.11/0.98  --add_important_lit                     false
% 1.11/0.98  --prop_solver_per_cl                    1000
% 1.11/0.98  --min_unsat_core                        false
% 1.11/0.98  --soft_assumptions                      false
% 1.11/0.98  --soft_lemma_size                       3
% 1.11/0.98  --prop_impl_unit_size                   0
% 1.11/0.98  --prop_impl_unit                        []
% 1.11/0.98  --share_sel_clauses                     true
% 1.11/0.98  --reset_solvers                         false
% 1.11/0.98  --bc_imp_inh                            [conj_cone]
% 1.11/0.98  --conj_cone_tolerance                   3.
% 1.11/0.98  --extra_neg_conj                        none
% 1.11/0.98  --large_theory_mode                     true
% 1.11/0.98  --prolific_symb_bound                   200
% 1.11/0.98  --lt_threshold                          2000
% 1.11/0.98  --clause_weak_htbl                      true
% 1.11/0.98  --gc_record_bc_elim                     false
% 1.11/0.98  
% 1.11/0.98  ------ Preprocessing Options
% 1.11/0.98  
% 1.11/0.98  --preprocessing_flag                    true
% 1.11/0.98  --time_out_prep_mult                    0.1
% 1.11/0.98  --splitting_mode                        input
% 1.11/0.98  --splitting_grd                         true
% 1.11/0.98  --splitting_cvd                         false
% 1.11/0.98  --splitting_cvd_svl                     false
% 1.11/0.98  --splitting_nvd                         32
% 1.11/0.98  --sub_typing                            true
% 1.11/0.98  --prep_gs_sim                           true
% 1.11/0.98  --prep_unflatten                        true
% 1.11/0.98  --prep_res_sim                          true
% 1.11/0.98  --prep_upred                            true
% 1.11/0.98  --prep_sem_filter                       exhaustive
% 1.11/0.98  --prep_sem_filter_out                   false
% 1.11/0.98  --pred_elim                             true
% 1.11/0.98  --res_sim_input                         true
% 1.11/0.98  --eq_ax_congr_red                       true
% 1.11/0.98  --pure_diseq_elim                       true
% 1.11/0.98  --brand_transform                       false
% 1.11/0.98  --non_eq_to_eq                          false
% 1.11/0.98  --prep_def_merge                        true
% 1.11/0.98  --prep_def_merge_prop_impl              false
% 1.11/0.98  --prep_def_merge_mbd                    true
% 1.11/0.98  --prep_def_merge_tr_red                 false
% 1.11/0.98  --prep_def_merge_tr_cl                  false
% 1.11/0.98  --smt_preprocessing                     true
% 1.11/0.98  --smt_ac_axioms                         fast
% 1.11/0.98  --preprocessed_out                      false
% 1.11/0.98  --preprocessed_stats                    false
% 1.11/0.98  
% 1.11/0.98  ------ Abstraction refinement Options
% 1.11/0.98  
% 1.11/0.98  --abstr_ref                             []
% 1.11/0.98  --abstr_ref_prep                        false
% 1.11/0.98  --abstr_ref_until_sat                   false
% 1.11/0.98  --abstr_ref_sig_restrict                funpre
% 1.11/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.11/0.98  --abstr_ref_under                       []
% 1.11/0.98  
% 1.11/0.98  ------ SAT Options
% 1.11/0.98  
% 1.11/0.98  --sat_mode                              false
% 1.11/0.98  --sat_fm_restart_options                ""
% 1.11/0.98  --sat_gr_def                            false
% 1.11/0.98  --sat_epr_types                         true
% 1.11/0.98  --sat_non_cyclic_types                  false
% 1.11/0.98  --sat_finite_models                     false
% 1.11/0.98  --sat_fm_lemmas                         false
% 1.11/0.98  --sat_fm_prep                           false
% 1.11/0.98  --sat_fm_uc_incr                        true
% 1.11/0.98  --sat_out_model                         small
% 1.11/0.98  --sat_out_clauses                       false
% 1.11/0.98  
% 1.11/0.98  ------ QBF Options
% 1.11/0.98  
% 1.11/0.98  --qbf_mode                              false
% 1.11/0.98  --qbf_elim_univ                         false
% 1.11/0.98  --qbf_dom_inst                          none
% 1.11/0.98  --qbf_dom_pre_inst                      false
% 1.11/0.98  --qbf_sk_in                             false
% 1.11/0.98  --qbf_pred_elim                         true
% 1.11/0.98  --qbf_split                             512
% 1.11/0.98  
% 1.11/0.98  ------ BMC1 Options
% 1.11/0.98  
% 1.11/0.98  --bmc1_incremental                      false
% 1.11/0.98  --bmc1_axioms                           reachable_all
% 1.11/0.98  --bmc1_min_bound                        0
% 1.11/0.98  --bmc1_max_bound                        -1
% 1.11/0.98  --bmc1_max_bound_default                -1
% 1.11/0.98  --bmc1_symbol_reachability              true
% 1.11/0.98  --bmc1_property_lemmas                  false
% 1.11/0.98  --bmc1_k_induction                      false
% 1.11/0.98  --bmc1_non_equiv_states                 false
% 1.11/0.98  --bmc1_deadlock                         false
% 1.11/0.98  --bmc1_ucm                              false
% 1.11/0.98  --bmc1_add_unsat_core                   none
% 1.11/0.98  --bmc1_unsat_core_children              false
% 1.11/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.11/0.98  --bmc1_out_stat                         full
% 1.11/0.98  --bmc1_ground_init                      false
% 1.11/0.98  --bmc1_pre_inst_next_state              false
% 1.11/0.98  --bmc1_pre_inst_state                   false
% 1.11/0.98  --bmc1_pre_inst_reach_state             false
% 1.11/0.98  --bmc1_out_unsat_core                   false
% 1.11/0.98  --bmc1_aig_witness_out                  false
% 1.11/0.98  --bmc1_verbose                          false
% 1.11/0.98  --bmc1_dump_clauses_tptp                false
% 1.11/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.11/0.98  --bmc1_dump_file                        -
% 1.11/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.11/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.11/0.98  --bmc1_ucm_extend_mode                  1
% 1.11/0.98  --bmc1_ucm_init_mode                    2
% 1.11/0.98  --bmc1_ucm_cone_mode                    none
% 1.11/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.11/0.98  --bmc1_ucm_relax_model                  4
% 1.11/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.11/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.11/0.98  --bmc1_ucm_layered_model                none
% 1.11/0.98  --bmc1_ucm_max_lemma_size               10
% 1.11/0.98  
% 1.11/0.98  ------ AIG Options
% 1.11/0.98  
% 1.11/0.98  --aig_mode                              false
% 1.11/0.98  
% 1.11/0.98  ------ Instantiation Options
% 1.11/0.98  
% 1.11/0.98  --instantiation_flag                    true
% 1.11/0.98  --inst_sos_flag                         false
% 1.11/0.98  --inst_sos_phase                        true
% 1.11/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.11/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.11/0.98  --inst_lit_sel_side                     none
% 1.11/0.98  --inst_solver_per_active                1400
% 1.11/0.98  --inst_solver_calls_frac                1.
% 1.11/0.98  --inst_passive_queue_type               priority_queues
% 1.11/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.11/0.98  --inst_passive_queues_freq              [25;2]
% 1.11/0.98  --inst_dismatching                      true
% 1.11/0.98  --inst_eager_unprocessed_to_passive     true
% 1.11/0.98  --inst_prop_sim_given                   true
% 1.11/0.98  --inst_prop_sim_new                     false
% 1.11/0.98  --inst_subs_new                         false
% 1.11/0.98  --inst_eq_res_simp                      false
% 1.11/0.98  --inst_subs_given                       false
% 1.11/0.98  --inst_orphan_elimination               true
% 1.11/0.98  --inst_learning_loop_flag               true
% 1.11/0.98  --inst_learning_start                   3000
% 1.11/0.98  --inst_learning_factor                  2
% 1.11/0.98  --inst_start_prop_sim_after_learn       3
% 1.11/0.98  --inst_sel_renew                        solver
% 1.11/0.98  --inst_lit_activity_flag                true
% 1.11/0.98  --inst_restr_to_given                   false
% 1.11/0.98  --inst_activity_threshold               500
% 1.11/0.98  --inst_out_proof                        true
% 1.11/0.98  
% 1.11/0.98  ------ Resolution Options
% 1.11/0.98  
% 1.11/0.98  --resolution_flag                       false
% 1.11/0.98  --res_lit_sel                           adaptive
% 1.11/0.98  --res_lit_sel_side                      none
% 1.11/0.98  --res_ordering                          kbo
% 1.11/0.98  --res_to_prop_solver                    active
% 1.11/0.98  --res_prop_simpl_new                    false
% 1.11/0.98  --res_prop_simpl_given                  true
% 1.11/0.98  --res_passive_queue_type                priority_queues
% 1.11/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.11/0.98  --res_passive_queues_freq               [15;5]
% 1.11/0.98  --res_forward_subs                      full
% 1.11/0.98  --res_backward_subs                     full
% 1.11/0.98  --res_forward_subs_resolution           true
% 1.11/0.98  --res_backward_subs_resolution          true
% 1.11/0.98  --res_orphan_elimination                true
% 1.11/0.98  --res_time_limit                        2.
% 1.11/0.98  --res_out_proof                         true
% 1.11/0.98  
% 1.11/0.98  ------ Superposition Options
% 1.11/0.98  
% 1.11/0.98  --superposition_flag                    true
% 1.11/0.98  --sup_passive_queue_type                priority_queues
% 1.11/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.11/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.11/0.98  --demod_completeness_check              fast
% 1.11/0.98  --demod_use_ground                      true
% 1.11/0.98  --sup_to_prop_solver                    passive
% 1.11/0.98  --sup_prop_simpl_new                    true
% 1.11/0.98  --sup_prop_simpl_given                  true
% 1.11/0.98  --sup_fun_splitting                     false
% 1.11/0.98  --sup_smt_interval                      50000
% 1.11/0.98  
% 1.11/0.98  ------ Superposition Simplification Setup
% 1.11/0.98  
% 1.11/0.98  --sup_indices_passive                   []
% 1.11/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.11/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/0.98  --sup_full_bw                           [BwDemod]
% 1.11/0.98  --sup_immed_triv                        [TrivRules]
% 1.11/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.11/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/0.98  --sup_immed_bw_main                     []
% 1.11/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.11/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.11/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.11/0.98  
% 1.11/0.98  ------ Combination Options
% 1.11/0.98  
% 1.11/0.98  --comb_res_mult                         3
% 1.11/0.98  --comb_sup_mult                         2
% 1.11/0.98  --comb_inst_mult                        10
% 1.11/0.98  
% 1.11/0.98  ------ Debug Options
% 1.11/0.98  
% 1.11/0.98  --dbg_backtrace                         false
% 1.11/0.98  --dbg_dump_prop_clauses                 false
% 1.11/0.98  --dbg_dump_prop_clauses_file            -
% 1.11/0.98  --dbg_out_stat                          false
% 1.11/0.98  
% 1.11/0.98  
% 1.11/0.98  
% 1.11/0.98  
% 1.11/0.98  ------ Proving...
% 1.11/0.98  
% 1.11/0.98  
% 1.11/0.98  % SZS status Theorem for theBenchmark.p
% 1.11/0.98  
% 1.11/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.11/0.98  
% 1.11/0.98  fof(f8,plain,(
% 1.11/0.98    ! [X2,X0] : ((v2_funct_1(X2) <=> ! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0))) | ~sP0(X2,X0))),
% 1.11/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.11/0.98  
% 1.11/0.98  fof(f10,plain,(
% 1.11/0.98    ! [X2,X0] : (((v2_funct_1(X2) | ? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | ~v2_funct_1(X2))) | ~sP0(X2,X0))),
% 1.11/0.98    inference(nnf_transformation,[],[f8])).
% 1.11/0.98  
% 1.11/0.98  fof(f11,plain,(
% 1.11/0.98    ! [X0,X1] : (((v2_funct_1(X0) | ? [X2,X3] : (X2 != X3 & k1_funct_1(X0,X2) = k1_funct_1(X0,X3) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X0,X4) != k1_funct_1(X0,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~v2_funct_1(X0))) | ~sP0(X0,X1))),
% 1.11/0.98    inference(rectify,[],[f10])).
% 1.11/0.98  
% 1.11/0.98  fof(f12,plain,(
% 1.11/0.98    ! [X1,X0] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X0,X2) = k1_funct_1(X0,X3) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (sK1(X0,X1) != sK2(X0,X1) & k1_funct_1(X0,sK1(X0,X1)) = k1_funct_1(X0,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK1(X0,X1),X1)))),
% 1.11/0.98    introduced(choice_axiom,[])).
% 1.11/0.98  
% 1.11/0.98  fof(f13,plain,(
% 1.11/0.98    ! [X0,X1] : (((v2_funct_1(X0) | (sK1(X0,X1) != sK2(X0,X1) & k1_funct_1(X0,sK1(X0,X1)) = k1_funct_1(X0,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK1(X0,X1),X1))) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X0,X4) != k1_funct_1(X0,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~v2_funct_1(X0))) | ~sP0(X0,X1))),
% 1.11/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f11,f12])).
% 1.11/0.98  
% 1.11/0.98  fof(f23,plain,(
% 1.11/0.98    ( ! [X0,X1] : (v2_funct_1(X0) | k1_funct_1(X0,sK1(X0,X1)) = k1_funct_1(X0,sK2(X0,X1)) | ~sP0(X0,X1)) )),
% 1.11/0.98    inference(cnf_transformation,[],[f13])).
% 1.11/0.98  
% 1.11/0.98  fof(f2,conjecture,(
% 1.11/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.11/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/0.98  
% 1.11/0.98  fof(f3,negated_conjecture,(
% 1.11/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.11/0.98    inference(negated_conjecture,[],[f2])).
% 1.11/0.98  
% 1.11/0.98  fof(f6,plain,(
% 1.11/0.98    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.11/0.98    inference(ennf_transformation,[],[f3])).
% 1.11/0.98  
% 1.11/0.98  fof(f7,plain,(
% 1.11/0.98    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.11/0.98    inference(flattening,[],[f6])).
% 1.11/0.98  
% 1.11/0.98  fof(f14,plain,(
% 1.11/0.98    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.11/0.98    inference(nnf_transformation,[],[f7])).
% 1.11/0.98  
% 1.11/0.98  fof(f15,plain,(
% 1.11/0.98    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.11/0.98    inference(flattening,[],[f14])).
% 1.11/0.98  
% 1.11/0.98  fof(f16,plain,(
% 1.11/0.98    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.11/0.98    inference(rectify,[],[f15])).
% 1.11/0.98  
% 1.11/0.98  fof(f18,plain,(
% 1.11/0.98    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK5 != sK6 & k1_funct_1(X1,sK5) = k1_funct_1(X1,sK6) & r2_hidden(sK6,X0) & r2_hidden(sK5,X0))) )),
% 1.11/0.98    introduced(choice_axiom,[])).
% 1.11/0.98  
% 1.11/0.98  fof(f17,plain,(
% 1.11/0.98    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK4,X2) = k1_funct_1(sK4,X3) & r2_hidden(X3,sK3) & r2_hidden(X2,sK3)) | ~v2_funct_1(sK4)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK3)) | v2_funct_1(sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4))),
% 1.11/0.98    introduced(choice_axiom,[])).
% 1.11/0.98  
% 1.11/0.98  fof(f19,plain,(
% 1.11/0.98    ((sK5 != sK6 & k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) & r2_hidden(sK6,sK3) & r2_hidden(sK5,sK3)) | ~v2_funct_1(sK4)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK3)) | v2_funct_1(sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4)),
% 1.11/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f16,f18,f17])).
% 1.11/0.98  
% 1.11/0.98  fof(f28,plain,(
% 1.11/0.98    v1_funct_2(sK4,sK3,sK3)),
% 1.11/0.98    inference(cnf_transformation,[],[f19])).
% 1.11/0.98  
% 1.11/0.98  fof(f1,axiom,(
% 1.11/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v2_funct_1(X2) <=> ! [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) => X3 = X4))))),
% 1.11/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/0.98  
% 1.11/0.98  fof(f4,plain,(
% 1.11/0.98    ! [X0,X1,X2] : (((v2_funct_1(X2) <=> ! [X3,X4] : (X3 = X4 | (k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.11/0.98    inference(ennf_transformation,[],[f1])).
% 1.11/0.98  
% 1.11/0.98  fof(f5,plain,(
% 1.11/0.98    ! [X0,X1,X2] : ((v2_funct_1(X2) <=> ! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.11/0.98    inference(flattening,[],[f4])).
% 1.11/0.98  
% 1.11/0.98  fof(f9,plain,(
% 1.11/0.98    ! [X0,X1,X2] : (sP0(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.11/0.98    inference(definition_folding,[],[f5,f8])).
% 1.11/0.98  
% 1.11/0.98  fof(f26,plain,(
% 1.11/0.98    ( ! [X2,X0,X1] : (sP0(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.11/0.98    inference(cnf_transformation,[],[f9])).
% 1.11/0.98  
% 1.11/0.98  fof(f35,plain,(
% 1.11/0.98    ( ! [X2,X1] : (sP0(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 1.11/0.98    inference(equality_resolution,[],[f26])).
% 1.11/0.98  
% 1.11/0.98  fof(f29,plain,(
% 1.11/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))),
% 1.11/0.98    inference(cnf_transformation,[],[f19])).
% 1.11/0.98  
% 1.11/0.98  fof(f27,plain,(
% 1.11/0.98    v1_funct_1(sK4)),
% 1.11/0.98    inference(cnf_transformation,[],[f19])).
% 1.11/0.98  
% 1.11/0.98  fof(f25,plain,(
% 1.11/0.98    ( ! [X2,X0,X1] : (sP0(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.11/0.98    inference(cnf_transformation,[],[f9])).
% 1.11/0.98  
% 1.11/0.98  fof(f31,plain,(
% 1.11/0.98    r2_hidden(sK5,sK3) | ~v2_funct_1(sK4)),
% 1.11/0.98    inference(cnf_transformation,[],[f19])).
% 1.11/0.98  
% 1.11/0.98  fof(f32,plain,(
% 1.11/0.98    r2_hidden(sK6,sK3) | ~v2_funct_1(sK4)),
% 1.11/0.98    inference(cnf_transformation,[],[f19])).
% 1.11/0.98  
% 1.11/0.98  fof(f34,plain,(
% 1.11/0.98    sK5 != sK6 | ~v2_funct_1(sK4)),
% 1.11/0.98    inference(cnf_transformation,[],[f19])).
% 1.11/0.98  
% 1.11/0.98  fof(f33,plain,(
% 1.11/0.98    k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) | ~v2_funct_1(sK4)),
% 1.11/0.98    inference(cnf_transformation,[],[f19])).
% 1.11/0.98  
% 1.11/0.98  fof(f20,plain,(
% 1.11/0.98    ( ! [X4,X0,X5,X1] : (X4 = X5 | k1_funct_1(X0,X4) != k1_funct_1(X0,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~v2_funct_1(X0) | ~sP0(X0,X1)) )),
% 1.11/0.98    inference(cnf_transformation,[],[f13])).
% 1.11/0.98  
% 1.11/0.98  fof(f30,plain,(
% 1.11/0.98    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK4,X4) != k1_funct_1(sK4,X5) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK3) | v2_funct_1(sK4)) )),
% 1.11/0.98    inference(cnf_transformation,[],[f19])).
% 1.11/0.98  
% 1.11/0.98  fof(f22,plain,(
% 1.11/0.98    ( ! [X0,X1] : (v2_funct_1(X0) | r2_hidden(sK2(X0,X1),X1) | ~sP0(X0,X1)) )),
% 1.11/0.98    inference(cnf_transformation,[],[f13])).
% 1.11/0.98  
% 1.11/0.98  fof(f21,plain,(
% 1.11/0.98    ( ! [X0,X1] : (v2_funct_1(X0) | r2_hidden(sK1(X0,X1),X1) | ~sP0(X0,X1)) )),
% 1.11/0.98    inference(cnf_transformation,[],[f13])).
% 1.11/0.98  
% 1.11/0.98  fof(f24,plain,(
% 1.11/0.98    ( ! [X0,X1] : (v2_funct_1(X0) | sK1(X0,X1) != sK2(X0,X1) | ~sP0(X0,X1)) )),
% 1.11/0.98    inference(cnf_transformation,[],[f13])).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1,plain,
% 1.11/0.98      ( ~ sP0(X0,X1)
% 1.11/0.98      | v2_funct_1(X0)
% 1.11/0.98      | k1_funct_1(X0,sK2(X0,X1)) = k1_funct_1(X0,sK1(X0,X1)) ),
% 1.11/0.98      inference(cnf_transformation,[],[f23]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_13,negated_conjecture,
% 1.11/0.98      ( v1_funct_2(sK4,sK3,sK3) ),
% 1.11/0.98      inference(cnf_transformation,[],[f28]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_5,plain,
% 1.11/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.11/0.98      | sP0(X0,k1_xboole_0)
% 1.11/0.98      | ~ v1_funct_1(X0) ),
% 1.11/0.98      inference(cnf_transformation,[],[f35]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_12,negated_conjecture,
% 1.11/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
% 1.11/0.98      inference(cnf_transformation,[],[f29]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_167,plain,
% 1.11/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.11/0.98      | sP0(X0,k1_xboole_0)
% 1.11/0.98      | ~ v1_funct_1(X0)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK4 != X0 ),
% 1.11/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_12]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_168,plain,
% 1.11/0.98      ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
% 1.11/0.98      | sP0(sK4,k1_xboole_0)
% 1.11/0.98      | ~ v1_funct_1(sK4)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
% 1.11/0.98      inference(unflattening,[status(thm)],[c_167]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_14,negated_conjecture,
% 1.11/0.98      ( v1_funct_1(sK4) ),
% 1.11/0.98      inference(cnf_transformation,[],[f27]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_172,plain,
% 1.11/0.98      ( sP0(sK4,k1_xboole_0)
% 1.11/0.98      | ~ v1_funct_2(sK4,k1_xboole_0,X0)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
% 1.11/0.98      inference(global_propositional_subsumption,
% 1.11/0.98                [status(thm)],
% 1.11/0.98                [c_168,c_14]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_173,plain,
% 1.11/0.98      ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
% 1.11/0.98      | sP0(sK4,k1_xboole_0)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
% 1.11/0.98      inference(renaming,[status(thm)],[c_172]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_221,plain,
% 1.11/0.98      ( sP0(sK4,k1_xboole_0)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != X0
% 1.11/0.98      | sK3 != k1_xboole_0
% 1.11/0.98      | sK4 != sK4 ),
% 1.11/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_173]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_222,plain,
% 1.11/0.98      ( sP0(sK4,k1_xboole_0)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0 ),
% 1.11/0.98      inference(unflattening,[status(thm)],[c_221]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_287,plain,
% 1.11/0.98      ( v2_funct_1(X0)
% 1.11/0.98      | k1_funct_1(X0,sK2(X0,X1)) = k1_funct_1(X0,sK1(X0,X1))
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0
% 1.11/0.98      | sK4 != X0
% 1.11/0.98      | k1_xboole_0 != X1 ),
% 1.11/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_222]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_288,plain,
% 1.11/0.98      ( v2_funct_1(sK4)
% 1.11/0.98      | k1_funct_1(sK4,sK2(sK4,k1_xboole_0)) = k1_funct_1(sK4,sK1(sK4,k1_xboole_0))
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0 ),
% 1.11/0.98      inference(unflattening,[status(thm)],[c_287]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1291,plain,
% 1.11/0.98      ( v2_funct_1(sK4)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | k1_funct_1(sK4,sK2(sK4,k1_xboole_0)) = k1_funct_1(sK4,sK1(sK4,k1_xboole_0))
% 1.11/0.98      | sK3 != k1_xboole_0 ),
% 1.11/0.98      inference(subtyping,[status(esa)],[c_288]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1581,plain,
% 1.11/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | k1_funct_1(sK4,sK2(sK4,k1_xboole_0)) = k1_funct_1(sK4,sK1(sK4,k1_xboole_0))
% 1.11/0.98      | sK3 != k1_xboole_0
% 1.11/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1291]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1303,plain,( X0_45 = X0_45 ),theory(equality) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1325,plain,
% 1.11/0.98      ( sK3 = sK3 ),
% 1.11/0.98      inference(instantiation,[status(thm)],[c_1303]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1336,plain,
% 1.11/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | k1_funct_1(sK4,sK2(sK4,k1_xboole_0)) = k1_funct_1(sK4,sK1(sK4,k1_xboole_0))
% 1.11/0.98      | sK3 != k1_xboole_0
% 1.11/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1291]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1316,plain,
% 1.11/0.98      ( X0_49 != X1_49 | k1_zfmisc_1(X0_49) = k1_zfmisc_1(X1_49) ),
% 1.11/0.98      theory(equality) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1777,plain,
% 1.11/0.98      ( k2_zfmisc_1(k1_xboole_0,sK3) != k2_zfmisc_1(sK3,sK3)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
% 1.11/0.98      inference(instantiation,[status(thm)],[c_1316]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1315,plain,
% 1.11/0.98      ( k2_zfmisc_1(X0_45,X1_45) = k2_zfmisc_1(X2_45,X3_45)
% 1.11/0.98      | X0_45 != X2_45
% 1.11/0.98      | X1_45 != X3_45 ),
% 1.11/0.98      theory(equality) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1783,plain,
% 1.11/0.98      ( k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(sK3,sK3)
% 1.11/0.98      | sK3 != sK3
% 1.11/0.98      | k1_xboole_0 != sK3 ),
% 1.11/0.98      inference(instantiation,[status(thm)],[c_1315]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1308,plain,
% 1.11/0.98      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 1.11/0.98      theory(equality) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1808,plain,
% 1.11/0.98      ( sK3 != X0_45 | k1_xboole_0 != X0_45 | k1_xboole_0 = sK3 ),
% 1.11/0.98      inference(instantiation,[status(thm)],[c_1308]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1847,plain,
% 1.11/0.98      ( sK3 != k1_xboole_0
% 1.11/0.98      | k1_xboole_0 = sK3
% 1.11/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 1.11/0.98      inference(instantiation,[status(thm)],[c_1808]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1848,plain,
% 1.11/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 1.11/0.98      inference(instantiation,[status(thm)],[c_1303]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_6,plain,
% 1.11/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.11/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.11/0.98      | sP0(X0,X1)
% 1.11/0.98      | ~ v1_funct_1(X0)
% 1.11/0.98      | k1_xboole_0 = X2 ),
% 1.11/0.98      inference(cnf_transformation,[],[f25]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_188,plain,
% 1.11/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.11/0.98      | sP0(X0,X1)
% 1.11/0.98      | ~ v1_funct_1(X0)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK4 != X0
% 1.11/0.98      | k1_xboole_0 = X2 ),
% 1.11/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_12]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_189,plain,
% 1.11/0.98      ( ~ v1_funct_2(sK4,X0,X1)
% 1.11/0.98      | sP0(sK4,X0)
% 1.11/0.98      | ~ v1_funct_1(sK4)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | k1_xboole_0 = X1 ),
% 1.11/0.98      inference(unflattening,[status(thm)],[c_188]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_193,plain,
% 1.11/0.98      ( sP0(sK4,X0)
% 1.11/0.98      | ~ v1_funct_2(sK4,X0,X1)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | k1_xboole_0 = X1 ),
% 1.11/0.98      inference(global_propositional_subsumption,
% 1.11/0.98                [status(thm)],
% 1.11/0.98                [c_189,c_14]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_194,plain,
% 1.11/0.98      ( ~ v1_funct_2(sK4,X0,X1)
% 1.11/0.98      | sP0(sK4,X0)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | k1_xboole_0 = X1 ),
% 1.11/0.98      inference(renaming,[status(thm)],[c_193]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_234,plain,
% 1.11/0.98      ( sP0(sK4,X0)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != X0
% 1.11/0.98      | sK3 != X1
% 1.11/0.98      | sK4 != sK4
% 1.11/0.98      | k1_xboole_0 = X1 ),
% 1.11/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_194]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_235,plain,
% 1.11/0.98      ( sP0(sK4,sK3)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | k1_xboole_0 = sK3 ),
% 1.11/0.98      inference(unflattening,[status(thm)],[c_234]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_345,plain,
% 1.11/0.98      ( v2_funct_1(X0)
% 1.11/0.98      | k1_funct_1(X0,sK2(X0,X1)) = k1_funct_1(X0,sK1(X0,X1))
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != X1
% 1.11/0.98      | sK3 = k1_xboole_0
% 1.11/0.98      | sK4 != X0 ),
% 1.11/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_235]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_346,plain,
% 1.11/0.98      ( v2_funct_1(sK4)
% 1.11/0.98      | k1_funct_1(sK4,sK2(sK4,sK3)) = k1_funct_1(sK4,sK1(sK4,sK3))
% 1.11/0.98      | sK3 = k1_xboole_0 ),
% 1.11/0.98      inference(unflattening,[status(thm)],[c_345]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1287,plain,
% 1.11/0.98      ( v2_funct_1(sK4)
% 1.11/0.98      | k1_funct_1(sK4,sK2(sK4,sK3)) = k1_funct_1(sK4,sK1(sK4,sK3))
% 1.11/0.98      | sK3 = k1_xboole_0 ),
% 1.11/0.98      inference(subtyping,[status(esa)],[c_346]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1585,plain,
% 1.11/0.98      ( k1_funct_1(sK4,sK2(sK4,sK3)) = k1_funct_1(sK4,sK1(sK4,sK3))
% 1.11/0.98      | sK3 = k1_xboole_0
% 1.11/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1287]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_10,negated_conjecture,
% 1.11/0.98      ( r2_hidden(sK5,sK3) | ~ v2_funct_1(sK4) ),
% 1.11/0.98      inference(cnf_transformation,[],[f31]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_21,plain,
% 1.11/0.98      ( r2_hidden(sK5,sK3) = iProver_top
% 1.11/0.98      | v2_funct_1(sK4) != iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_9,negated_conjecture,
% 1.11/0.98      ( r2_hidden(sK6,sK3) | ~ v2_funct_1(sK4) ),
% 1.11/0.98      inference(cnf_transformation,[],[f32]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_22,plain,
% 1.11/0.98      ( r2_hidden(sK6,sK3) = iProver_top
% 1.11/0.98      | v2_funct_1(sK4) != iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_7,negated_conjecture,
% 1.11/0.98      ( ~ v2_funct_1(sK4) | sK5 != sK6 ),
% 1.11/0.98      inference(cnf_transformation,[],[f34]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1298,negated_conjecture,
% 1.11/0.98      ( ~ v2_funct_1(sK4) | sK5 != sK6 ),
% 1.11/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1329,plain,
% 1.11/0.98      ( sK5 != sK6 | v2_funct_1(sK4) != iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1298]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_8,negated_conjecture,
% 1.11/0.98      ( ~ v2_funct_1(sK4) | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
% 1.11/0.98      inference(cnf_transformation,[],[f33]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1297,negated_conjecture,
% 1.11/0.98      ( ~ v2_funct_1(sK4) | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
% 1.11/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1330,plain,
% 1.11/0.98      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
% 1.11/0.98      | v2_funct_1(sK4) != iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1297]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1340,plain,
% 1.11/0.98      ( k1_funct_1(sK4,sK2(sK4,sK3)) = k1_funct_1(sK4,sK1(sK4,sK3))
% 1.11/0.98      | sK3 = k1_xboole_0
% 1.11/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1287]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_4,plain,
% 1.11/0.98      ( ~ r2_hidden(X0,X1)
% 1.11/0.98      | ~ r2_hidden(X2,X1)
% 1.11/0.98      | ~ sP0(X3,X1)
% 1.11/0.98      | ~ v2_funct_1(X3)
% 1.11/0.98      | X0 = X2
% 1.11/0.98      | k1_funct_1(X3,X0) != k1_funct_1(X3,X2) ),
% 1.11/0.98      inference(cnf_transformation,[],[f20]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_398,plain,
% 1.11/0.98      ( ~ r2_hidden(X0,X1)
% 1.11/0.98      | ~ r2_hidden(X2,X1)
% 1.11/0.98      | ~ v2_funct_1(X3)
% 1.11/0.98      | X0 = X2
% 1.11/0.98      | k1_funct_1(X3,X0) != k1_funct_1(X3,X2)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != X1
% 1.11/0.98      | sK3 = k1_xboole_0
% 1.11/0.98      | sK4 != X3 ),
% 1.11/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_235]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_399,plain,
% 1.11/0.98      ( ~ r2_hidden(X0,sK3)
% 1.11/0.98      | ~ r2_hidden(X1,sK3)
% 1.11/0.98      | ~ v2_funct_1(sK4)
% 1.11/0.98      | X1 = X0
% 1.11/0.98      | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0)
% 1.11/0.98      | sK3 = k1_xboole_0 ),
% 1.11/0.98      inference(unflattening,[status(thm)],[c_398]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_11,negated_conjecture,
% 1.11/0.98      ( ~ r2_hidden(X0,sK3)
% 1.11/0.98      | ~ r2_hidden(X1,sK3)
% 1.11/0.98      | v2_funct_1(sK4)
% 1.11/0.98      | X1 = X0
% 1.11/0.98      | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0) ),
% 1.11/0.98      inference(cnf_transformation,[],[f30]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_403,plain,
% 1.11/0.98      ( ~ r2_hidden(X1,sK3)
% 1.11/0.98      | ~ r2_hidden(X0,sK3)
% 1.11/0.98      | X1 = X0
% 1.11/0.98      | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0)
% 1.11/0.98      | sK3 = k1_xboole_0 ),
% 1.11/0.98      inference(global_propositional_subsumption,
% 1.11/0.98                [status(thm)],
% 1.11/0.98                [c_399,c_11]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_404,plain,
% 1.11/0.98      ( ~ r2_hidden(X0,sK3)
% 1.11/0.98      | ~ r2_hidden(X1,sK3)
% 1.11/0.98      | X1 = X0
% 1.11/0.98      | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0)
% 1.11/0.98      | sK3 = k1_xboole_0 ),
% 1.11/0.98      inference(renaming,[status(thm)],[c_403]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1284,plain,
% 1.11/0.98      ( ~ r2_hidden(X0_44,sK3)
% 1.11/0.98      | ~ r2_hidden(X1_44,sK3)
% 1.11/0.98      | k1_funct_1(sK4,X1_44) != k1_funct_1(sK4,X0_44)
% 1.11/0.98      | sK3 = k1_xboole_0
% 1.11/0.98      | X1_44 = X0_44 ),
% 1.11/0.98      inference(subtyping,[status(esa)],[c_404]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1739,plain,
% 1.11/0.98      ( ~ r2_hidden(sK6,sK3)
% 1.11/0.98      | ~ r2_hidden(sK5,sK3)
% 1.11/0.98      | k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
% 1.11/0.98      | sK3 = k1_xboole_0
% 1.11/0.98      | sK5 = sK6 ),
% 1.11/0.98      inference(instantiation,[status(thm)],[c_1284]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1740,plain,
% 1.11/0.98      ( k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
% 1.11/0.98      | sK3 = k1_xboole_0
% 1.11/0.98      | sK5 = sK6
% 1.11/0.98      | r2_hidden(sK6,sK3) != iProver_top
% 1.11/0.98      | r2_hidden(sK5,sK3) != iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1739]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1870,plain,
% 1.11/0.98      ( sK3 = k1_xboole_0
% 1.11/0.98      | k1_funct_1(sK4,sK2(sK4,sK3)) = k1_funct_1(sK4,sK1(sK4,sK3)) ),
% 1.11/0.98      inference(global_propositional_subsumption,
% 1.11/0.98                [status(thm)],
% 1.11/0.98                [c_1585,c_21,c_22,c_1329,c_1330,c_1340,c_1740]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1871,plain,
% 1.11/0.98      ( k1_funct_1(sK4,sK2(sK4,sK3)) = k1_funct_1(sK4,sK1(sK4,sK3))
% 1.11/0.98      | sK3 = k1_xboole_0 ),
% 1.11/0.98      inference(renaming,[status(thm)],[c_1870]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1294,negated_conjecture,
% 1.11/0.98      ( ~ r2_hidden(X0_44,sK3)
% 1.11/0.98      | ~ r2_hidden(X1_44,sK3)
% 1.11/0.98      | v2_funct_1(sK4)
% 1.11/0.98      | k1_funct_1(sK4,X1_44) != k1_funct_1(sK4,X0_44)
% 1.11/0.98      | X1_44 = X0_44 ),
% 1.11/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1578,plain,
% 1.11/0.98      ( k1_funct_1(sK4,X0_44) != k1_funct_1(sK4,X1_44)
% 1.11/0.98      | X0_44 = X1_44
% 1.11/0.98      | r2_hidden(X0_44,sK3) != iProver_top
% 1.11/0.98      | r2_hidden(X1_44,sK3) != iProver_top
% 1.11/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1294]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1874,plain,
% 1.11/0.98      ( k1_funct_1(sK4,sK1(sK4,sK3)) != k1_funct_1(sK4,X0_44)
% 1.11/0.98      | sK3 = k1_xboole_0
% 1.11/0.98      | sK2(sK4,sK3) = X0_44
% 1.11/0.98      | r2_hidden(X0_44,sK3) != iProver_top
% 1.11/0.98      | r2_hidden(sK2(sK4,sK3),sK3) != iProver_top
% 1.11/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.11/0.98      inference(superposition,[status(thm)],[c_1871,c_1578]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_2,plain,
% 1.11/0.98      ( r2_hidden(sK2(X0,X1),X1) | ~ sP0(X0,X1) | v2_funct_1(X0) ),
% 1.11/0.98      inference(cnf_transformation,[],[f22]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_332,plain,
% 1.11/0.98      ( r2_hidden(sK2(X0,X1),X1)
% 1.11/0.98      | v2_funct_1(X0)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != X1
% 1.11/0.98      | sK3 = k1_xboole_0
% 1.11/0.98      | sK4 != X0 ),
% 1.11/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_235]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_333,plain,
% 1.11/0.98      ( r2_hidden(sK2(sK4,sK3),sK3)
% 1.11/0.98      | v2_funct_1(sK4)
% 1.11/0.98      | sK3 = k1_xboole_0 ),
% 1.11/0.98      inference(unflattening,[status(thm)],[c_332]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1288,plain,
% 1.11/0.98      ( r2_hidden(sK2(sK4,sK3),sK3)
% 1.11/0.98      | v2_funct_1(sK4)
% 1.11/0.98      | sK3 = k1_xboole_0 ),
% 1.11/0.98      inference(subtyping,[status(esa)],[c_333]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1584,plain,
% 1.11/0.98      ( sK3 = k1_xboole_0
% 1.11/0.98      | r2_hidden(sK2(sK4,sK3),sK3) = iProver_top
% 1.11/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1288]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1339,plain,
% 1.11/0.98      ( sK3 = k1_xboole_0
% 1.11/0.98      | r2_hidden(sK2(sK4,sK3),sK3) = iProver_top
% 1.11/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1288]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1830,plain,
% 1.11/0.98      ( r2_hidden(sK2(sK4,sK3),sK3) = iProver_top | sK3 = k1_xboole_0 ),
% 1.11/0.98      inference(global_propositional_subsumption,
% 1.11/0.98                [status(thm)],
% 1.11/0.98                [c_1584,c_21,c_22,c_1329,c_1330,c_1339,c_1740]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1831,plain,
% 1.11/0.98      ( sK3 = k1_xboole_0 | r2_hidden(sK2(sK4,sK3),sK3) = iProver_top ),
% 1.11/0.98      inference(renaming,[status(thm)],[c_1830]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1911,plain,
% 1.11/0.98      ( k1_funct_1(sK4,sK1(sK4,sK3)) != k1_funct_1(sK4,X0_44)
% 1.11/0.98      | sK3 = k1_xboole_0
% 1.11/0.98      | sK2(sK4,sK3) = X0_44
% 1.11/0.98      | r2_hidden(X0_44,sK3) != iProver_top ),
% 1.11/0.98      inference(global_propositional_subsumption,
% 1.11/0.98                [status(thm)],
% 1.11/0.98                [c_1874,c_21,c_22,c_1329,c_1330,c_1339,c_1740]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1922,plain,
% 1.11/0.98      ( sK3 = k1_xboole_0
% 1.11/0.98      | sK2(sK4,sK3) = sK1(sK4,sK3)
% 1.11/0.98      | r2_hidden(sK1(sK4,sK3),sK3) != iProver_top ),
% 1.11/0.98      inference(equality_resolution,[status(thm)],[c_1911]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_3,plain,
% 1.11/0.98      ( r2_hidden(sK1(X0,X1),X1) | ~ sP0(X0,X1) | v2_funct_1(X0) ),
% 1.11/0.98      inference(cnf_transformation,[],[f21]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_319,plain,
% 1.11/0.98      ( r2_hidden(sK1(X0,X1),X1)
% 1.11/0.98      | v2_funct_1(X0)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != X1
% 1.11/0.98      | sK3 = k1_xboole_0
% 1.11/0.98      | sK4 != X0 ),
% 1.11/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_235]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_320,plain,
% 1.11/0.98      ( r2_hidden(sK1(sK4,sK3),sK3)
% 1.11/0.98      | v2_funct_1(sK4)
% 1.11/0.98      | sK3 = k1_xboole_0 ),
% 1.11/0.98      inference(unflattening,[status(thm)],[c_319]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1289,plain,
% 1.11/0.98      ( r2_hidden(sK1(sK4,sK3),sK3)
% 1.11/0.98      | v2_funct_1(sK4)
% 1.11/0.98      | sK3 = k1_xboole_0 ),
% 1.11/0.98      inference(subtyping,[status(esa)],[c_320]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1583,plain,
% 1.11/0.98      ( sK3 = k1_xboole_0
% 1.11/0.98      | r2_hidden(sK1(sK4,sK3),sK3) = iProver_top
% 1.11/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1289]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1338,plain,
% 1.11/0.98      ( sK3 = k1_xboole_0
% 1.11/0.98      | r2_hidden(sK1(sK4,sK3),sK3) = iProver_top
% 1.11/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1289]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1823,plain,
% 1.11/0.98      ( r2_hidden(sK1(sK4,sK3),sK3) = iProver_top | sK3 = k1_xboole_0 ),
% 1.11/0.98      inference(global_propositional_subsumption,
% 1.11/0.98                [status(thm)],
% 1.11/0.98                [c_1583,c_21,c_22,c_1329,c_1330,c_1338,c_1740]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1824,plain,
% 1.11/0.98      ( sK3 = k1_xboole_0 | r2_hidden(sK1(sK4,sK3),sK3) = iProver_top ),
% 1.11/0.98      inference(renaming,[status(thm)],[c_1823]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_0,plain,
% 1.11/0.98      ( ~ sP0(X0,X1) | v2_funct_1(X0) | sK2(X0,X1) != sK1(X0,X1) ),
% 1.11/0.98      inference(cnf_transformation,[],[f24]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_358,plain,
% 1.11/0.98      ( v2_funct_1(X0)
% 1.11/0.98      | sK2(X0,X1) != sK1(X0,X1)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != X1
% 1.11/0.98      | sK3 = k1_xboole_0
% 1.11/0.98      | sK4 != X0 ),
% 1.11/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_235]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_359,plain,
% 1.11/0.98      ( v2_funct_1(sK4)
% 1.11/0.98      | sK2(sK4,sK3) != sK1(sK4,sK3)
% 1.11/0.98      | sK3 = k1_xboole_0 ),
% 1.11/0.98      inference(unflattening,[status(thm)],[c_358]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1286,plain,
% 1.11/0.98      ( v2_funct_1(sK4)
% 1.11/0.98      | sK3 = k1_xboole_0
% 1.11/0.98      | sK2(sK4,sK3) != sK1(sK4,sK3) ),
% 1.11/0.98      inference(subtyping,[status(esa)],[c_359]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1586,plain,
% 1.11/0.98      ( sK3 = k1_xboole_0
% 1.11/0.98      | sK2(sK4,sK3) != sK1(sK4,sK3)
% 1.11/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1286]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1341,plain,
% 1.11/0.98      ( sK3 = k1_xboole_0
% 1.11/0.98      | sK2(sK4,sK3) != sK1(sK4,sK3)
% 1.11/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1286]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1865,plain,
% 1.11/0.98      ( sK2(sK4,sK3) != sK1(sK4,sK3) | sK3 = k1_xboole_0 ),
% 1.11/0.98      inference(global_propositional_subsumption,
% 1.11/0.98                [status(thm)],
% 1.11/0.98                [c_1586,c_21,c_22,c_1329,c_1330,c_1341,c_1740]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1866,plain,
% 1.11/0.98      ( sK3 = k1_xboole_0 | sK2(sK4,sK3) != sK1(sK4,sK3) ),
% 1.11/0.98      inference(renaming,[status(thm)],[c_1865]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_2001,plain,
% 1.11/0.98      ( sK3 = k1_xboole_0 ),
% 1.11/0.98      inference(global_propositional_subsumption,
% 1.11/0.98                [status(thm)],
% 1.11/0.98                [c_1922,c_1824,c_1866]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1295,negated_conjecture,
% 1.11/0.98      ( r2_hidden(sK5,sK3) | ~ v2_funct_1(sK4) ),
% 1.11/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1577,plain,
% 1.11/0.98      ( r2_hidden(sK5,sK3) = iProver_top
% 1.11/0.98      | v2_funct_1(sK4) != iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1295]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_2010,plain,
% 1.11/0.98      ( r2_hidden(sK5,k1_xboole_0) = iProver_top
% 1.11/0.98      | v2_funct_1(sK4) != iProver_top ),
% 1.11/0.98      inference(demodulation,[status(thm)],[c_2001,c_1577]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_371,plain,
% 1.11/0.98      ( ~ r2_hidden(X0,X1)
% 1.11/0.98      | ~ r2_hidden(X2,X1)
% 1.11/0.98      | ~ v2_funct_1(X3)
% 1.11/0.98      | X0 = X2
% 1.11/0.98      | k1_funct_1(X3,X0) != k1_funct_1(X3,X2)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0
% 1.11/0.98      | sK4 != X3
% 1.11/0.98      | k1_xboole_0 != X1 ),
% 1.11/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_222]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_372,plain,
% 1.11/0.98      ( ~ r2_hidden(X0,k1_xboole_0)
% 1.11/0.98      | ~ r2_hidden(X1,k1_xboole_0)
% 1.11/0.98      | ~ v2_funct_1(sK4)
% 1.11/0.98      | X1 = X0
% 1.11/0.98      | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0 ),
% 1.11/0.98      inference(unflattening,[status(thm)],[c_371]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1285,plain,
% 1.11/0.98      ( ~ r2_hidden(X0_44,k1_xboole_0)
% 1.11/0.98      | ~ r2_hidden(X1_44,k1_xboole_0)
% 1.11/0.98      | ~ v2_funct_1(sK4)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | k1_funct_1(sK4,X1_44) != k1_funct_1(sK4,X0_44)
% 1.11/0.98      | sK3 != k1_xboole_0
% 1.11/0.98      | X1_44 = X0_44 ),
% 1.11/0.98      inference(subtyping,[status(esa)],[c_372]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1300,plain,
% 1.11/0.98      ( ~ v2_funct_1(sK4)
% 1.11/0.98      | sP0_iProver_split
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0 ),
% 1.11/0.98      inference(splitting,
% 1.11/0.98                [splitting(split),new_symbols(definition,[])],
% 1.11/0.98                [c_1285]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1342,plain,
% 1.11/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0
% 1.11/0.98      | v2_funct_1(sK4) != iProver_top
% 1.11/0.98      | sP0_iProver_split = iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1300]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1299,plain,
% 1.11/0.98      ( ~ r2_hidden(X0_44,k1_xboole_0)
% 1.11/0.98      | ~ r2_hidden(X1_44,k1_xboole_0)
% 1.11/0.98      | k1_funct_1(sK4,X1_44) != k1_funct_1(sK4,X0_44)
% 1.11/0.98      | X1_44 = X0_44
% 1.11/0.98      | ~ sP0_iProver_split ),
% 1.11/0.98      inference(splitting,
% 1.11/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.11/0.98                [c_1285]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1879,plain,
% 1.11/0.98      ( ~ r2_hidden(sK6,k1_xboole_0)
% 1.11/0.98      | ~ r2_hidden(sK5,k1_xboole_0)
% 1.11/0.98      | ~ sP0_iProver_split
% 1.11/0.98      | k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
% 1.11/0.98      | sK5 = sK6 ),
% 1.11/0.98      inference(instantiation,[status(thm)],[c_1299]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1880,plain,
% 1.11/0.98      ( k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
% 1.11/0.98      | sK5 = sK6
% 1.11/0.98      | r2_hidden(sK6,k1_xboole_0) != iProver_top
% 1.11/0.98      | r2_hidden(sK5,k1_xboole_0) != iProver_top
% 1.11/0.98      | sP0_iProver_split != iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1879]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1296,negated_conjecture,
% 1.11/0.98      ( r2_hidden(sK6,sK3) | ~ v2_funct_1(sK4) ),
% 1.11/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1576,plain,
% 1.11/0.98      ( r2_hidden(sK6,sK3) = iProver_top
% 1.11/0.98      | v2_funct_1(sK4) != iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1296]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_2011,plain,
% 1.11/0.98      ( r2_hidden(sK6,k1_xboole_0) = iProver_top
% 1.11/0.98      | v2_funct_1(sK4) != iProver_top ),
% 1.11/0.98      inference(demodulation,[status(thm)],[c_2001,c_1576]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_2052,plain,
% 1.11/0.98      ( v2_funct_1(sK4) != iProver_top ),
% 1.11/0.98      inference(global_propositional_subsumption,
% 1.11/0.98                [status(thm)],
% 1.11/0.98                [c_2010,c_1325,c_1329,c_1330,c_1342,c_1777,c_1783,c_1824,
% 1.11/0.98                 c_1847,c_1848,c_1866,c_1880,c_1922,c_2011]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_2214,plain,
% 1.11/0.98      ( k1_funct_1(sK4,sK2(sK4,k1_xboole_0)) = k1_funct_1(sK4,sK1(sK4,k1_xboole_0)) ),
% 1.11/0.98      inference(global_propositional_subsumption,
% 1.11/0.98                [status(thm)],
% 1.11/0.98                [c_1581,c_1325,c_1329,c_1330,c_1336,c_1342,c_1777,c_1783,
% 1.11/0.98                 c_1824,c_1847,c_1848,c_1866,c_1880,c_1922,c_2010,c_2011]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_2009,plain,
% 1.11/0.98      ( k1_funct_1(sK4,X0_44) != k1_funct_1(sK4,X1_44)
% 1.11/0.98      | X1_44 = X0_44
% 1.11/0.98      | r2_hidden(X1_44,k1_xboole_0) != iProver_top
% 1.11/0.98      | r2_hidden(X0_44,k1_xboole_0) != iProver_top
% 1.11/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.11/0.98      inference(demodulation,[status(thm)],[c_2001,c_1578]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_2113,plain,
% 1.11/0.98      ( r2_hidden(X0_44,k1_xboole_0) != iProver_top
% 1.11/0.98      | r2_hidden(X1_44,k1_xboole_0) != iProver_top
% 1.11/0.98      | X1_44 = X0_44
% 1.11/0.98      | k1_funct_1(sK4,X0_44) != k1_funct_1(sK4,X1_44) ),
% 1.11/0.98      inference(global_propositional_subsumption,
% 1.11/0.98                [status(thm)],
% 1.11/0.98                [c_2009,c_1325,c_1329,c_1330,c_1342,c_1777,c_1783,c_1824,
% 1.11/0.98                 c_1847,c_1848,c_1866,c_1880,c_1922,c_2010,c_2011]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_2114,plain,
% 1.11/0.98      ( k1_funct_1(sK4,X0_44) != k1_funct_1(sK4,X1_44)
% 1.11/0.98      | X1_44 = X0_44
% 1.11/0.98      | r2_hidden(X1_44,k1_xboole_0) != iProver_top
% 1.11/0.98      | r2_hidden(X0_44,k1_xboole_0) != iProver_top ),
% 1.11/0.98      inference(renaming,[status(thm)],[c_2113]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_2219,plain,
% 1.11/0.98      ( k1_funct_1(sK4,sK1(sK4,k1_xboole_0)) != k1_funct_1(sK4,X0_44)
% 1.11/0.98      | sK2(sK4,k1_xboole_0) = X0_44
% 1.11/0.98      | r2_hidden(X0_44,k1_xboole_0) != iProver_top
% 1.11/0.98      | r2_hidden(sK2(sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 1.11/0.98      inference(superposition,[status(thm)],[c_2214,c_2114]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_271,plain,
% 1.11/0.98      ( r2_hidden(sK2(X0,X1),X1)
% 1.11/0.98      | v2_funct_1(X0)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0
% 1.11/0.98      | sK4 != X0
% 1.11/0.98      | k1_xboole_0 != X1 ),
% 1.11/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_222]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_272,plain,
% 1.11/0.98      ( r2_hidden(sK2(sK4,k1_xboole_0),k1_xboole_0)
% 1.11/0.98      | v2_funct_1(sK4)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0 ),
% 1.11/0.98      inference(unflattening,[status(thm)],[c_271]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1292,plain,
% 1.11/0.98      ( r2_hidden(sK2(sK4,k1_xboole_0),k1_xboole_0)
% 1.11/0.98      | v2_funct_1(sK4)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0 ),
% 1.11/0.98      inference(subtyping,[status(esa)],[c_272]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1335,plain,
% 1.11/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0
% 1.11/0.98      | r2_hidden(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top
% 1.11/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1292]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_2279,plain,
% 1.11/0.98      ( r2_hidden(X0_44,k1_xboole_0) != iProver_top
% 1.11/0.98      | sK2(sK4,k1_xboole_0) = X0_44
% 1.11/0.98      | k1_funct_1(sK4,sK1(sK4,k1_xboole_0)) != k1_funct_1(sK4,X0_44) ),
% 1.11/0.98      inference(global_propositional_subsumption,
% 1.11/0.98                [status(thm)],
% 1.11/0.98                [c_2219,c_1325,c_1329,c_1330,c_1335,c_1342,c_1777,c_1783,
% 1.11/0.98                 c_1824,c_1847,c_1848,c_1866,c_1880,c_1922,c_2010,c_2011]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_2280,plain,
% 1.11/0.98      ( k1_funct_1(sK4,sK1(sK4,k1_xboole_0)) != k1_funct_1(sK4,X0_44)
% 1.11/0.98      | sK2(sK4,k1_xboole_0) = X0_44
% 1.11/0.98      | r2_hidden(X0_44,k1_xboole_0) != iProver_top ),
% 1.11/0.98      inference(renaming,[status(thm)],[c_2279]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_2289,plain,
% 1.11/0.98      ( sK2(sK4,k1_xboole_0) = sK1(sK4,k1_xboole_0)
% 1.11/0.98      | r2_hidden(sK1(sK4,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 1.11/0.98      inference(equality_resolution,[status(thm)],[c_2280]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_303,plain,
% 1.11/0.98      ( v2_funct_1(X0)
% 1.11/0.98      | sK2(X0,X1) != sK1(X0,X1)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0
% 1.11/0.98      | sK4 != X0
% 1.11/0.98      | k1_xboole_0 != X1 ),
% 1.11/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_222]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_304,plain,
% 1.11/0.98      ( v2_funct_1(sK4)
% 1.11/0.98      | sK2(sK4,k1_xboole_0) != sK1(sK4,k1_xboole_0)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0 ),
% 1.11/0.98      inference(unflattening,[status(thm)],[c_303]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1290,plain,
% 1.11/0.98      ( v2_funct_1(sK4)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0
% 1.11/0.98      | sK2(sK4,k1_xboole_0) != sK1(sK4,k1_xboole_0) ),
% 1.11/0.98      inference(subtyping,[status(esa)],[c_304]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1337,plain,
% 1.11/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0
% 1.11/0.98      | sK2(sK4,k1_xboole_0) != sK1(sK4,k1_xboole_0)
% 1.11/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1290]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_255,plain,
% 1.11/0.98      ( r2_hidden(sK1(X0,X1),X1)
% 1.11/0.98      | v2_funct_1(X0)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0
% 1.11/0.98      | sK4 != X0
% 1.11/0.98      | k1_xboole_0 != X1 ),
% 1.11/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_222]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_256,plain,
% 1.11/0.98      ( r2_hidden(sK1(sK4,k1_xboole_0),k1_xboole_0)
% 1.11/0.98      | v2_funct_1(sK4)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0 ),
% 1.11/0.98      inference(unflattening,[status(thm)],[c_255]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1293,plain,
% 1.11/0.98      ( r2_hidden(sK1(sK4,k1_xboole_0),k1_xboole_0)
% 1.11/0.98      | v2_funct_1(sK4)
% 1.11/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0 ),
% 1.11/0.98      inference(subtyping,[status(esa)],[c_256]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(c_1334,plain,
% 1.11/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 1.11/0.98      | sK3 != k1_xboole_0
% 1.11/0.98      | r2_hidden(sK1(sK4,k1_xboole_0),k1_xboole_0) = iProver_top
% 1.11/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.11/0.98      inference(predicate_to_equality,[status(thm)],[c_1293]) ).
% 1.11/0.98  
% 1.11/0.98  cnf(contradiction,plain,
% 1.11/0.98      ( $false ),
% 1.11/0.98      inference(minisat,
% 1.11/0.98                [status(thm)],
% 1.11/0.98                [c_2289,c_2052,c_2001,c_1848,c_1847,c_1783,c_1777,c_1337,
% 1.11/0.98                 c_1334,c_1325]) ).
% 1.11/0.98  
% 1.11/0.98  
% 1.11/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.11/0.98  
% 1.11/0.98  ------                               Statistics
% 1.11/0.98  
% 1.11/0.98  ------ General
% 1.11/0.98  
% 1.11/0.98  abstr_ref_over_cycles:                  0
% 1.11/0.98  abstr_ref_under_cycles:                 0
% 1.11/0.98  gc_basic_clause_elim:                   0
% 1.11/0.98  forced_gc_time:                         0
% 1.11/0.98  parsing_time:                           0.009
% 1.11/0.98  unif_index_cands_time:                  0.
% 1.11/0.98  unif_index_add_time:                    0.
% 1.11/0.98  orderings_time:                         0.
% 1.11/0.98  out_proof_time:                         0.012
% 1.11/0.98  total_time:                             0.072
% 1.11/0.98  num_of_symbols:                         51
% 1.11/0.98  num_of_terms:                           949
% 1.11/0.98  
% 1.11/0.98  ------ Preprocessing
% 1.11/0.98  
% 1.11/0.98  num_of_splits:                          1
% 1.11/0.98  num_of_split_atoms:                     1
% 1.11/0.98  num_of_reused_defs:                     0
% 1.11/0.98  num_eq_ax_congr_red:                    9
% 1.11/0.98  num_of_sem_filtered_clauses:            1
% 1.11/0.98  num_of_subtypes:                        6
% 1.11/0.98  monotx_restored_types:                  0
% 1.11/0.98  sat_num_of_epr_types:                   0
% 1.11/0.98  sat_num_of_non_cyclic_types:            0
% 1.11/0.98  sat_guarded_non_collapsed_types:        1
% 1.11/0.98  num_pure_diseq_elim:                    0
% 1.11/0.98  simp_replaced_by:                       0
% 1.11/0.98  res_preprocessed:                       78
% 1.11/0.98  prep_upred:                             0
% 1.11/0.98  prep_unflattend:                        25
% 1.11/0.98  smt_new_axioms:                         0
% 1.11/0.98  pred_elim_cands:                        6
% 1.11/0.98  pred_elim:                              4
% 1.11/0.98  pred_elim_cl:                           0
% 1.11/0.98  pred_elim_cycles:                       5
% 1.11/0.98  merged_defs:                            0
% 1.11/0.98  merged_defs_ncl:                        0
% 1.11/0.98  bin_hyper_res:                          0
% 1.11/0.98  prep_cycles:                            3
% 1.11/0.98  pred_elim_time:                         0.013
% 1.11/0.98  splitting_time:                         0.
% 1.11/0.98  sem_filter_time:                        0.
% 1.11/0.98  monotx_time:                            0.
% 1.11/0.98  subtype_inf_time:                       0.
% 1.11/0.98  
% 1.11/0.98  ------ Problem properties
% 1.11/0.98  
% 1.11/0.98  clauses:                                16
% 1.11/0.98  conjectures:                            5
% 1.11/0.98  epr:                                    3
% 1.11/0.98  horn:                                   7
% 1.11/0.98  ground:                                 13
% 1.11/0.98  unary:                                  0
% 1.11/0.98  binary:                                 4
% 1.11/0.98  lits:                                   55
% 1.11/0.98  lits_eq:                                27
% 1.11/0.98  fd_pure:                                0
% 1.11/0.98  fd_pseudo:                              0
% 1.11/0.98  fd_cond:                                0
% 1.11/0.98  fd_pseudo_cond:                         3
% 1.11/0.98  ac_symbols:                             0
% 1.11/0.98  
% 1.11/0.98  ------ Propositional Solver
% 1.11/0.98  
% 1.11/0.98  prop_solver_calls:                      25
% 1.11/0.98  prop_fast_solver_calls:                 785
% 1.11/0.98  smt_solver_calls:                       0
% 1.11/0.98  smt_fast_solver_calls:                  0
% 1.11/0.98  prop_num_of_clauses:                    415
% 1.11/0.98  prop_preprocess_simplified:             1895
% 1.11/0.98  prop_fo_subsumed:                       28
% 1.11/0.98  prop_solver_time:                       0.
% 1.11/0.98  smt_solver_time:                        0.
% 1.11/0.98  smt_fast_solver_time:                   0.
% 1.11/0.98  prop_fast_solver_time:                  0.
% 1.11/0.98  prop_unsat_core_time:                   0.
% 1.11/0.98  
% 1.11/0.98  ------ QBF
% 1.11/0.98  
% 1.11/0.98  qbf_q_res:                              0
% 1.11/0.98  qbf_num_tautologies:                    0
% 1.11/0.98  qbf_prep_cycles:                        0
% 1.11/0.98  
% 1.11/0.98  ------ BMC1
% 1.11/0.98  
% 1.11/0.98  bmc1_current_bound:                     -1
% 1.11/0.98  bmc1_last_solved_bound:                 -1
% 1.11/0.98  bmc1_unsat_core_size:                   -1
% 1.11/0.98  bmc1_unsat_core_parents_size:           -1
% 1.11/0.98  bmc1_merge_next_fun:                    0
% 1.11/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.11/0.98  
% 1.11/0.98  ------ Instantiation
% 1.11/0.98  
% 1.11/0.98  inst_num_of_clauses:                    105
% 1.11/0.98  inst_num_in_passive:                    18
% 1.11/0.98  inst_num_in_active:                     80
% 1.11/0.98  inst_num_in_unprocessed:                7
% 1.11/0.98  inst_num_of_loops:                      110
% 1.11/0.98  inst_num_of_learning_restarts:          0
% 1.11/0.98  inst_num_moves_active_passive:          22
% 1.11/0.98  inst_lit_activity:                      0
% 1.11/0.98  inst_lit_activity_moves:                0
% 1.11/0.98  inst_num_tautologies:                   0
% 1.11/0.98  inst_num_prop_implied:                  0
% 1.11/0.98  inst_num_existing_simplified:           0
% 1.11/0.98  inst_num_eq_res_simplified:             0
% 1.11/0.98  inst_num_child_elim:                    0
% 1.11/0.98  inst_num_of_dismatching_blockings:      20
% 1.11/0.98  inst_num_of_non_proper_insts:           109
% 1.11/0.98  inst_num_of_duplicates:                 0
% 1.11/0.98  inst_inst_num_from_inst_to_res:         0
% 1.11/0.98  inst_dismatching_checking_time:         0.
% 1.11/0.98  
% 1.11/0.98  ------ Resolution
% 1.11/0.98  
% 1.11/0.98  res_num_of_clauses:                     0
% 1.11/0.98  res_num_in_passive:                     0
% 1.11/0.98  res_num_in_active:                      0
% 1.11/0.98  res_num_of_loops:                       81
% 1.11/0.98  res_forward_subset_subsumed:            27
% 1.11/0.98  res_backward_subset_subsumed:           0
% 1.11/0.98  res_forward_subsumed:                   0
% 1.11/0.98  res_backward_subsumed:                  0
% 1.11/0.98  res_forward_subsumption_resolution:     0
% 1.11/0.98  res_backward_subsumption_resolution:    0
% 1.11/0.98  res_clause_to_clause_subsumption:       35
% 1.11/0.98  res_orphan_elimination:                 0
% 1.11/0.98  res_tautology_del:                      29
% 1.11/0.98  res_num_eq_res_simplified:              0
% 1.11/0.98  res_num_sel_changes:                    0
% 1.11/0.98  res_moves_from_active_to_pass:          0
% 1.11/0.98  
% 1.11/0.98  ------ Superposition
% 1.11/0.98  
% 1.11/0.98  sup_time_total:                         0.
% 1.11/0.98  sup_time_generating:                    0.
% 1.11/0.98  sup_time_sim_full:                      0.
% 1.11/0.98  sup_time_sim_immed:                     0.
% 1.11/0.98  
% 1.11/0.98  sup_num_of_clauses:                     15
% 1.11/0.98  sup_num_in_active:                      11
% 1.11/0.98  sup_num_in_passive:                     4
% 1.11/0.98  sup_num_of_loops:                       21
% 1.11/0.98  sup_fw_superposition:                   4
% 1.11/0.98  sup_bw_superposition:                   6
% 1.11/0.98  sup_immediate_simplified:               1
% 1.11/0.98  sup_given_eliminated:                   0
% 1.11/0.98  comparisons_done:                       0
% 1.11/0.98  comparisons_avoided:                    3
% 1.11/0.98  
% 1.11/0.98  ------ Simplifications
% 1.11/0.98  
% 1.11/0.98  
% 1.11/0.98  sim_fw_subset_subsumed:                 0
% 1.11/0.98  sim_bw_subset_subsumed:                 5
% 1.11/0.98  sim_fw_subsumed:                        0
% 1.11/0.98  sim_bw_subsumed:                        0
% 1.11/0.98  sim_fw_subsumption_res:                 0
% 1.11/0.98  sim_bw_subsumption_res:                 0
% 1.11/0.98  sim_tautology_del:                      0
% 1.11/0.98  sim_eq_tautology_del:                   7
% 1.11/0.98  sim_eq_res_simp:                        3
% 1.11/0.98  sim_fw_demodulated:                     0
% 1.11/0.98  sim_bw_demodulated:                     8
% 1.11/0.98  sim_light_normalised:                   0
% 1.11/0.98  sim_joinable_taut:                      0
% 1.11/0.98  sim_joinable_simp:                      0
% 1.11/0.98  sim_ac_normalised:                      0
% 1.11/0.98  sim_smt_subsumption:                    0
% 1.11/0.98  
%------------------------------------------------------------------------------
