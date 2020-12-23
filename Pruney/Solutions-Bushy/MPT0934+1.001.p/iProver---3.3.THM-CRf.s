%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0934+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:27 EST 2020

% Result     : Theorem 0.70s
% Output     : CNFRefutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 111 expanded)
%              Number of clauses        :   23 (  27 expanded)
%              Number of leaves         :    6 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  164 ( 655 expanded)
%              Number of equality atoms :   75 ( 307 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( k2_mcart_1(X0) = k2_mcart_1(X2)
            & k1_mcart_1(X0) = k1_mcart_1(X2)
            & r2_hidden(X0,X1)
            & r2_hidden(X2,X1) )
         => X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X0 = X2
          | k2_mcart_1(X0) != k2_mcart_1(X2)
          | k1_mcart_1(X0) != k1_mcart_1(X2)
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X2,X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X0 = X2
          | k2_mcart_1(X0) != k2_mcart_1(X2)
          | k1_mcart_1(X0) != k1_mcart_1(X2)
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X2,X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | k2_mcart_1(X0) != k2_mcart_1(X2)
      | k1_mcart_1(X0) != k1_mcart_1(X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ( k2_mcart_1(X1) = k2_mcart_1(X2)
                  & k1_mcart_1(X1) = k1_mcart_1(X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_relat_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ( k2_mcart_1(X1) = k2_mcart_1(X2)
                    & k1_mcart_1(X1) = k1_mcart_1(X2) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X1) = k2_mcart_1(X2)
              & k1_mcart_1(X1) = k1_mcart_1(X2)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X1) = k2_mcart_1(X2)
              & k1_mcart_1(X1) = k1_mcart_1(X2)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k2_mcart_1(X1) = k2_mcart_1(X2)
          & k1_mcart_1(X1) = k1_mcart_1(X2)
          & m1_subset_1(X2,X0) )
     => ( sK2 != X1
        & k2_mcart_1(sK2) = k2_mcart_1(X1)
        & k1_mcart_1(sK2) = k1_mcart_1(X1)
        & m1_subset_1(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X1) = k2_mcart_1(X2)
              & k1_mcart_1(X1) = k1_mcart_1(X2)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
     => ( ? [X2] :
            ( sK1 != X2
            & k2_mcart_1(sK1) = k2_mcart_1(X2)
            & k1_mcart_1(sK1) = k1_mcart_1(X2)
            & m1_subset_1(X2,X0) )
        & m1_subset_1(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k2_mcart_1(X1) = k2_mcart_1(X2)
                & k1_mcart_1(X1) = k1_mcart_1(X2)
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,X0) )
        & v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X1) = k2_mcart_1(X2)
              & k1_mcart_1(X1) = k1_mcart_1(X2)
              & m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,sK0) )
      & v1_relat_1(sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( sK1 != sK2
    & k2_mcart_1(sK1) = k2_mcart_1(sK2)
    & k1_mcart_1(sK1) = k1_mcart_1(sK2)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0)
    & v1_relat_1(sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13,f12,f11])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    k1_mcart_1(sK1) = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    k2_mcart_1(sK1) = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f17,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | k1_mcart_1(X2) != k1_mcart_1(X0)
    | k2_mcart_1(X2) != k2_mcart_1(X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_7,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_102,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | X2 = X0
    | k1_mcart_1(X2) != k1_mcart_1(X0)
    | k2_mcart_1(X2) != k2_mcart_1(X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_103,plain,
    ( ~ r2_hidden(X0,sK0)
    | ~ r2_hidden(X1,sK0)
    | X1 = X0
    | k1_mcart_1(X1) != k1_mcart_1(X0)
    | k2_mcart_1(X1) != k2_mcart_1(X0) ),
    inference(unflattening,[status(thm)],[c_102])).

cnf(c_153,plain,
    ( ~ r2_hidden(X0_37,sK0)
    | ~ r2_hidden(X1_37,sK0)
    | k2_mcart_1(X1_37) != k2_mcart_1(X0_37)
    | k1_mcart_1(X1_37) != k1_mcart_1(X0_37)
    | X1_37 = X0_37 ),
    inference(subtyping,[status(esa)],[c_103])).

cnf(c_261,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ r2_hidden(sK1,sK0)
    | k2_mcart_1(sK1) != k2_mcart_1(sK2)
    | k1_mcart_1(sK1) != k1_mcart_1(sK2)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_4,negated_conjecture,
    ( k1_mcart_1(sK1) = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_156,negated_conjecture,
    ( k1_mcart_1(sK1) = k1_mcart_1(sK2) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3,negated_conjecture,
    ( k2_mcart_1(sK1) = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_157,negated_conjecture,
    ( k2_mcart_1(sK1) = k2_mcart_1(sK2) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_158,negated_conjecture,
    ( sK1 != sK2 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_8,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_69,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_70,plain,
    ( ~ m1_subset_1(X0,sK0)
    | r2_hidden(X0,sK0) ),
    inference(unflattening,[status(thm)],[c_69])).

cnf(c_91,plain,
    ( r2_hidden(X0,sK0)
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_70])).

cnf(c_92,plain,
    ( r2_hidden(sK1,sK0) ),
    inference(unflattening,[status(thm)],[c_91])).

cnf(c_5,negated_conjecture,
    ( m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_84,plain,
    ( r2_hidden(X0,sK0)
    | sK0 != sK0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_70])).

cnf(c_85,plain,
    ( r2_hidden(sK2,sK0) ),
    inference(unflattening,[status(thm)],[c_84])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_261,c_156,c_157,c_158,c_92,c_85])).


%------------------------------------------------------------------------------
