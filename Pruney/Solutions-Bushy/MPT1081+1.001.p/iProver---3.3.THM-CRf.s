%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1081+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:50 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   61 (  85 expanded)
%              Number of clauses        :   30 (  30 expanded)
%              Number of leaves         :   10 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :  238 ( 375 expanded)
%              Number of equality atoms :   49 (  49 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( m1_subset_1(X3,X2)
           => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
            | ~ m1_subset_1(X3,X2) ) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
              | ~ m1_subset_1(X3,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
          & m1_subset_1(X3,X2) )
     => ( ( ~ m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(sK0(X0,X1,X2),X0,X1)
          | ~ v1_funct_1(sK0(X0,X1,X2)) )
        & m1_subset_1(sK0(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ( ( ~ m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(sK0(X0,X1,X2),X0,X1)
              | ~ v1_funct_1(sK0(X0,X1,X2)) )
            & m1_subset_1(sK0(X0,X1,X2),X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( m1_funct_2(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),X2)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => m1_funct_2(k1_tarski(X2),X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => m1_funct_2(k1_tarski(X2),X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_funct_2(k1_tarski(X2),X0,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_funct_2(k1_tarski(X2),X0,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ m1_funct_2(k1_tarski(X2),X0,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ m1_funct_2(k1_tarski(sK4),sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ m1_funct_2(k1_tarski(sK4),sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f11,f20])).

fof(f33,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( m1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK0(X0,X1,X2),X0,X1)
      | ~ v1_funct_1(sK0(X0,X1,X2))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f36,plain,(
    ~ m1_funct_2(k1_tarski(sK4),sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_523,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_878,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | X1 != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_925,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | X0 != sK4
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_878])).

cnf(c_1503,plain,
    ( m1_subset_1(sK0(sK2,sK3,k1_tarski(X0)),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK0(sK2,sK3,k1_tarski(X0)) != sK4
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_925])).

cnf(c_1505,plain,
    ( m1_subset_1(sK0(sK2,sK3,k1_tarski(sK4)),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK0(sK2,sK3,k1_tarski(sK4)) != sK4
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1503])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_866,plain,
    ( r2_hidden(X0,k1_tarski(X1))
    | ~ m1_subset_1(X0,k1_tarski(X1))
    | v1_xboole_0(k1_tarski(X1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1048,plain,
    ( r2_hidden(sK0(sK2,sK3,k1_tarski(X0)),k1_tarski(sK4))
    | ~ m1_subset_1(sK0(sK2,sK3,k1_tarski(X0)),k1_tarski(sK4))
    | v1_xboole_0(k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_1050,plain,
    ( r2_hidden(sK0(sK2,sK3,k1_tarski(sK4)),k1_tarski(sK4))
    | ~ m1_subset_1(sK0(sK2,sK3,k1_tarski(sK4)),k1_tarski(sK4))
    | v1_xboole_0(k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_1048])).

cnf(c_1,plain,
    ( m1_funct_2(X0,X1,X2)
    | m1_subset_1(sK0(X1,X2,X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_869,plain,
    ( m1_funct_2(k1_tarski(X0),X1,X2)
    | m1_subset_1(sK0(X1,X2,k1_tarski(X0)),k1_tarski(X0))
    | v1_xboole_0(k1_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_970,plain,
    ( m1_funct_2(k1_tarski(sK4),sK2,sK3)
    | m1_subset_1(sK0(sK2,sK3,k1_tarski(sK4)),k1_tarski(sK4))
    | v1_xboole_0(k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_869])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_938,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,k1_tarski(X0)),k1_tarski(sK4))
    | sK0(sK2,sK3,k1_tarski(X0)) = sK4 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_940,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,k1_tarski(sK4)),k1_tarski(sK4))
    | sK0(sK2,sK3,k1_tarski(sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_938])).

cnf(c_517,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_926,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_0,plain,
    ( ~ v1_funct_2(sK0(X0,X1,X2),X0,X1)
    | m1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(sK0(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_13,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_192,plain,
    ( m1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X0)
    | ~ v1_funct_1(sK0(X1,X2,X0))
    | sK0(X1,X2,X0) != sK4
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_193,plain,
    ( m1_funct_2(X0,sK2,sK3)
    | ~ m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_xboole_0(X0)
    | ~ v1_funct_1(sK0(sK2,sK3,X0))
    | sK0(sK2,sK3,X0) != sK4 ),
    inference(unflattening,[status(thm)],[c_192])).

cnf(c_252,plain,
    ( m1_funct_2(X0,sK2,sK3)
    | ~ m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_xboole_0(X0)
    | sK0(sK2,sK3,X0) != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_193])).

cnf(c_861,plain,
    ( m1_funct_2(k1_tarski(X0),sK2,sK3)
    | ~ m1_subset_1(sK0(sK2,sK3,k1_tarski(X0)),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_xboole_0(k1_tarski(X0))
    | sK0(sK2,sK3,k1_tarski(X0)) != sK4 ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_863,plain,
    ( m1_funct_2(k1_tarski(sK4),sK2,sK3)
    | ~ m1_subset_1(sK0(sK2,sK3,k1_tarski(sK4)),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_xboole_0(k1_tarski(sK4))
    | sK0(sK2,sK3,k1_tarski(sK4)) != sK4 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_9,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_23,plain,
    ( ~ v1_xboole_0(k1_tarski(sK4)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_11,negated_conjecture,
    ( ~ m1_funct_2(k1_tarski(sK4),sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1505,c_1050,c_970,c_940,c_926,c_863,c_23,c_11,c_12])).


%------------------------------------------------------------------------------
