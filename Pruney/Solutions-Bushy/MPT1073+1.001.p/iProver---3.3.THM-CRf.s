%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1073+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:49 EST 2020

% Result     : Theorem 0.75s
% Output     : CNFRefutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   45 (  98 expanded)
%              Number of clauses        :   24 (  27 expanded)
%              Number of leaves         :    5 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :  157 ( 485 expanded)
%              Number of equality atoms :   34 (  89 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f8])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK4,X4) != sK1
          | ~ m1_subset_1(X4,sK2) )
      & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ! [X4] :
        ( k1_funct_1(sK4,X4) != sK1
        | ~ m1_subset_1(X4,sK2) )
    & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f9,f12])).

fof(f21,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) != sK1
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f5])).

fof(f10,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X3,sK0(X0,X2,X3)) = X2
        & r2_hidden(sK0(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_funct_1(X3,sK0(X0,X2,X3)) = X2
        & r2_hidden(sK0(X0,X2,X3),X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f10])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X3,sK0(X0,X2,X3)) = X2
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f13])).

fof(f19,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK0(X0,X2,X3),X0)
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f20,plain,(
    r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_2,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_3,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | k1_funct_1(sK4,X0) != sK1 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_135,plain,
    ( ~ r2_hidden(X0,X1)
    | X2 != X0
    | k1_funct_1(sK4,X2) != sK1
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_136,plain,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK4,X0) != sK1 ),
    inference(unflattening,[status(thm)],[c_135])).

cnf(c_197,plain,
    ( ~ r2_hidden(X0_41,sK2)
    | k1_funct_1(sK4,X0_41) != sK1 ),
    inference(subtyping,[status(esa)],[c_136])).

cnf(c_350,plain,
    ( ~ r2_hidden(sK0(sK2,sK1,sK4),sK2)
    | k1_funct_1(sK4,sK0(sK2,sK1,sK4)) != sK1 ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK0(X1,X3,X0)) = X3 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_6,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_111,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK0(X1,X3,X0)) = X3
    | sK3 != X2
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_112,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r2_hidden(X0,k2_relset_1(sK2,sK3,sK4))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(sK4,sK0(sK2,X0,sK4)) = X0 ),
    inference(unflattening,[status(thm)],[c_111])).

cnf(c_7,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_5,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_116,plain,
    ( ~ r2_hidden(X0,k2_relset_1(sK2,sK3,sK4))
    | k1_funct_1(sK4,sK0(sK2,X0,sK4)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_112,c_7,c_5])).

cnf(c_198,plain,
    ( ~ r2_hidden(X0_41,k2_relset_1(sK2,sK3,sK4))
    | k1_funct_1(sK4,sK0(sK2,X0_41,sK4)) = X0_41 ),
    inference(subtyping,[status(esa)],[c_116])).

cnf(c_336,plain,
    ( ~ r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
    | k1_funct_1(sK4,sK0(sK2,sK1,sK4)) = sK1 ),
    inference(instantiation,[status(thm)],[c_198])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
    | r2_hidden(sK0(X1,X3,X0),X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_93,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
    | r2_hidden(sK0(X1,X3,X0),X1)
    | ~ v1_funct_1(X0)
    | sK3 != X2
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_6])).

cnf(c_94,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r2_hidden(X0,k2_relset_1(sK2,sK3,sK4))
    | r2_hidden(sK0(sK2,X0,sK4),sK2)
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_93])).

cnf(c_98,plain,
    ( r2_hidden(sK0(sK2,X0,sK4),sK2)
    | ~ r2_hidden(X0,k2_relset_1(sK2,sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_94,c_7,c_5])).

cnf(c_99,plain,
    ( ~ r2_hidden(X0,k2_relset_1(sK2,sK3,sK4))
    | r2_hidden(sK0(sK2,X0,sK4),sK2) ),
    inference(renaming,[status(thm)],[c_98])).

cnf(c_199,plain,
    ( ~ r2_hidden(X0_41,k2_relset_1(sK2,sK3,sK4))
    | r2_hidden(sK0(sK2,X0_41,sK4),sK2) ),
    inference(subtyping,[status(esa)],[c_99])).

cnf(c_333,plain,
    ( r2_hidden(sK0(sK2,sK1,sK4),sK2)
    | ~ r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_199])).

cnf(c_4,negated_conjecture,
    ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_350,c_336,c_333,c_4])).


%------------------------------------------------------------------------------
