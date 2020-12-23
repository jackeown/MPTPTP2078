%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1012+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:59 EST 2020

% Result     : Timeout 58.65s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   53 (  75 expanded)
%              Number of clauses        :   19 (  20 expanded)
%              Number of leaves         :   11 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  178 ( 266 expanded)
%              Number of equality atoms :   66 (  89 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1676,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f4653,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1676])).

fof(f1543,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1544,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f1543])).

fof(f3169,plain,(
    ? [X0,X1] :
      ( k1_relset_1(X0,X0,X1) != X0
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1544])).

fof(f3170,plain,(
    ? [X0,X1] :
      ( k1_relset_1(X0,X0,X1) != X0
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f3169])).

fof(f4455,plain,
    ( ? [X0,X1] :
        ( k1_relset_1(X0,X0,X1) != X0
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( k1_relset_1(sK540,sK540,sK541) != sK540
      & m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK540,sK540)))
      & v1_funct_2(sK541,sK540,sK540)
      & v1_funct_1(sK541) ) ),
    introduced(choice_axiom,[])).

fof(f4456,plain,
    ( k1_relset_1(sK540,sK540,sK541) != sK540
    & m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK540,sK540)))
    & v1_funct_2(sK541,sK540,sK540)
    & v1_funct_1(sK541) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK540,sK541])],[f3170,f4455])).

fof(f7364,plain,(
    m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK540,sK540))) ),
    inference(cnf_transformation,[],[f4456])).

fof(f1472,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3048,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1472])).

fof(f3049,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f3048])).

fof(f4399,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f3049])).

fof(f7167,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f4399])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4464,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f8412,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | o_0_0_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f7167,f4464])).

fof(f1245,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2837,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f1245])).

fof(f4066,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f2837])).

fof(f4067,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f4066])).

fof(f4069,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK336(X1,X2),X6),X2)
        & r2_hidden(sK336(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f4068,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK335(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f4070,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK335(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK336(X1,X2),X6),X2)
            & r2_hidden(sK336(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK335,sK336])],[f4067,f4069,f4068])).

fof(f6594,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK336(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f4070])).

fof(f1429,axiom,
    ( v1_xboole_0(k1_wellord2(k1_xboole_0))
    & v1_relat_1(k1_wellord2(k1_xboole_0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7048,plain,(
    v1_xboole_0(k1_wellord2(k1_xboole_0)) ),
    inference(cnf_transformation,[],[f1429])).

fof(f8393,plain,(
    v1_xboole_0(k1_wellord2(o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f7048,f4464])).

fof(f1430,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( ~ v1_xboole_0(k1_wellord2(X0))
        & v1_relat_1(k1_wellord2(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3002,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(k1_wellord2(X0))
        & v1_relat_1(k1_wellord2(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1430])).

fof(f7050,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_wellord2(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3002])).

fof(f7365,plain,(
    k1_relset_1(sK540,sK540,sK541) != sK540 ),
    inference(cnf_transformation,[],[f4456])).

fof(f7363,plain,(
    v1_funct_2(sK541,sK540,sK540) ),
    inference(cnf_transformation,[],[f4456])).

cnf(c_195,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f4653])).

cnf(c_194656,plain,
    ( ~ r2_hidden(sK336(sK540,sK541),sK540)
    | ~ v1_xboole_0(sK540) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_2882,negated_conjecture,
    ( m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK540,sK540))) ),
    inference(cnf_transformation,[],[f7364])).

cnf(c_83048,plain,
    ( m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK540,sK540))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2882])).

cnf(c_2692,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f8412])).

cnf(c_83223,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | o_0_0_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2692])).

cnf(c_147772,plain,
    ( k1_relset_1(sK540,sK540,sK541) = sK540
    | sK540 = o_0_0_xboole_0
    | v1_funct_2(sK541,sK540,sK540) != iProver_top ),
    inference(superposition,[status(thm)],[c_83048,c_83223])).

cnf(c_41268,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_131743,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK540)
    | sK540 != X0 ),
    inference(instantiation,[status(thm)],[c_41268])).

cnf(c_131751,plain,
    ( v1_xboole_0(sK540)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | sK540 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_131743])).

cnf(c_2124,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK336(X1,X0),X1)
    | k1_relset_1(X1,X2,X0) = X1 ),
    inference(cnf_transformation,[],[f6594])).

cnf(c_123815,plain,
    ( ~ m1_subset_1(sK541,k1_zfmisc_1(k2_zfmisc_1(sK540,sK540)))
    | r2_hidden(sK336(sK540,sK541),sK540)
    | k1_relset_1(sK540,sK540,sK541) = sK540 ),
    inference(instantiation,[status(thm)],[c_2124])).

cnf(c_2567,plain,
    ( v1_xboole_0(k1_wellord2(o_0_0_xboole_0)) ),
    inference(cnf_transformation,[],[f8393])).

cnf(c_2569,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f7050])).

cnf(c_3812,plain,
    ( ~ v1_xboole_0(k1_wellord2(o_0_0_xboole_0))
    | v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2569])).

cnf(c_2881,negated_conjecture,
    ( k1_relset_1(sK540,sK540,sK541) != sK540 ),
    inference(cnf_transformation,[],[f7365])).

cnf(c_2883,negated_conjecture,
    ( v1_funct_2(sK541,sK540,sK540) ),
    inference(cnf_transformation,[],[f7363])).

cnf(c_2900,plain,
    ( v1_funct_2(sK541,sK540,sK540) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2883])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_194656,c_147772,c_131751,c_123815,c_2567,c_3812,c_2881,c_2882,c_2900])).

%------------------------------------------------------------------------------
