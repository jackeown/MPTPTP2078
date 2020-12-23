%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1025+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:42 EST 2020

% Result     : Theorem 0.81s
% Output     : CNFRefutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 146 expanded)
%              Number of clauses        :   31 (  37 expanded)
%              Number of leaves         :    6 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  213 ( 863 expanded)
%              Number of equality atoms :   39 ( 141 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   14 (   3 average)
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

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f8])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK5
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK5,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK4,X5) != X4
              | ~ r2_hidden(X5,sK3)
              | ~ m1_subset_1(X5,sK1) )
          & r2_hidden(X4,k7_relset_1(sK1,sK2,sK4,sK3)) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ! [X5] :
        ( k1_funct_1(sK4,X5) != sK5
        | ~ r2_hidden(X5,sK3)
        | ~ m1_subset_1(X5,sK1) )
    & r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f9,f13,f12])).

fof(f23,plain,(
    ! [X5] :
      ( k1_funct_1(sK4,X5) != sK5
      | ~ r2_hidden(X5,sK3)
      | ~ m1_subset_1(X5,sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f5])).

fof(f10,plain,(
    ! [X4,X3,X2,X0] :
      ( ? [X5] :
          ( k1_funct_1(X3,X5) = X4
          & r2_hidden(X5,X2)
          & r2_hidden(X5,X0) )
     => ( k1_funct_1(X3,sK0(X0,X2,X3,X4)) = X4
        & r2_hidden(sK0(X0,X2,X3,X4),X2)
        & r2_hidden(sK0(X0,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k1_funct_1(X3,sK0(X0,X2,X3,X4)) = X4
            & r2_hidden(sK0(X0,X2,X3,X4),X2)
            & r2_hidden(sK0(X0,X2,X3,X4),X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f10])).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK0(X0,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f20,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f14])).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_funct_1(X3,sK0(X0,X2,X3,X4)) = X4
      | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK0(X0,X2,X3,X4),X0)
      | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_4,negated_conjecture,
    ( ~ m1_subset_1(X0,sK1)
    | ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK4,X0) != sK5 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_164,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,sK3)
    | X2 != X0
    | k1_funct_1(sK4,X2) != sK5
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_165,plain,
    ( ~ r2_hidden(X0,sK1)
    | ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK4,X0) != sK5 ),
    inference(unflattening,[status(thm)],[c_164])).

cnf(c_249,plain,
    ( ~ r2_hidden(X0_42,sK1)
    | ~ r2_hidden(X0_42,sK3)
    | k1_funct_1(sK4,X0_42) != sK5 ),
    inference(subtyping,[status(esa)],[c_165])).

cnf(c_451,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,sK4,sK5),sK1)
    | ~ r2_hidden(sK0(sK1,sK3,sK4,sK5),sK3)
    | k1_funct_1(sK4,sK0(sK1,sK3,sK4,sK5)) != sK5 ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k7_relset_1(X1,X2,X0,X4))
    | r2_hidden(sK0(X1,X4,X0,X3),X4)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_7,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_119,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k7_relset_1(X1,X2,X0,X4))
    | r2_hidden(sK0(X1,X4,X0,X3),X4)
    | ~ v1_funct_1(X0)
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_120,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ r2_hidden(X0,k7_relset_1(sK1,sK2,sK4,X1))
    | r2_hidden(sK0(sK1,X1,sK4,X0),X1)
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_119])).

cnf(c_8,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_124,plain,
    ( r2_hidden(sK0(sK1,X1,sK4,X0),X1)
    | ~ r2_hidden(X0,k7_relset_1(sK1,sK2,sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_120,c_8,c_6])).

cnf(c_125,plain,
    ( ~ r2_hidden(X0,k7_relset_1(sK1,sK2,sK4,X1))
    | r2_hidden(sK0(sK1,X1,sK4,X0),X1) ),
    inference(renaming,[status(thm)],[c_124])).

cnf(c_251,plain,
    ( ~ r2_hidden(X0_42,k7_relset_1(sK1,sK2,sK4,X0_43))
    | r2_hidden(sK0(sK1,X0_43,sK4,X0_42),X0_43) ),
    inference(subtyping,[status(esa)],[c_125])).

cnf(c_436,plain,
    ( r2_hidden(sK0(sK1,sK3,sK4,sK5),sK3)
    | ~ r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_251])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k7_relset_1(X1,X2,X0,X4))
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK0(X1,X4,X0,X3)) = X3 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_137,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k7_relset_1(X1,X2,X0,X4))
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK0(X1,X4,X0,X3)) = X3
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_138,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ r2_hidden(X0,k7_relset_1(sK1,sK2,sK4,X1))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(sK4,sK0(sK1,X1,sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_137])).

cnf(c_142,plain,
    ( ~ r2_hidden(X0,k7_relset_1(sK1,sK2,sK4,X1))
    | k1_funct_1(sK4,sK0(sK1,X1,sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_138,c_8,c_6])).

cnf(c_250,plain,
    ( ~ r2_hidden(X0_42,k7_relset_1(sK1,sK2,sK4,X0_43))
    | k1_funct_1(sK4,sK0(sK1,X0_43,sK4,X0_42)) = X0_42 ),
    inference(subtyping,[status(esa)],[c_142])).

cnf(c_433,plain,
    ( ~ r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3))
    | k1_funct_1(sK4,sK0(sK1,sK3,sK4,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k7_relset_1(X1,X2,X0,X4))
    | r2_hidden(sK0(X1,X4,X0,X3),X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_101,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k7_relset_1(X1,X2,X0,X4))
    | r2_hidden(sK0(X1,X4,X0,X3),X1)
    | ~ v1_funct_1(X0)
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_7])).

cnf(c_102,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ r2_hidden(X0,k7_relset_1(sK1,sK2,sK4,X1))
    | r2_hidden(sK0(sK1,X1,sK4,X0),sK1)
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_101])).

cnf(c_106,plain,
    ( r2_hidden(sK0(sK1,X1,sK4,X0),sK1)
    | ~ r2_hidden(X0,k7_relset_1(sK1,sK2,sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_102,c_8,c_6])).

cnf(c_107,plain,
    ( ~ r2_hidden(X0,k7_relset_1(sK1,sK2,sK4,X1))
    | r2_hidden(sK0(sK1,X1,sK4,X0),sK1) ),
    inference(renaming,[status(thm)],[c_106])).

cnf(c_252,plain,
    ( ~ r2_hidden(X0_42,k7_relset_1(sK1,sK2,sK4,X0_43))
    | r2_hidden(sK0(sK1,X0_43,sK4,X0_42),sK1) ),
    inference(subtyping,[status(esa)],[c_107])).

cnf(c_430,plain,
    ( r2_hidden(sK0(sK1,sK3,sK4,sK5),sK1)
    | ~ r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_5,negated_conjecture,
    ( r2_hidden(sK5,k7_relset_1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_451,c_436,c_433,c_430,c_5])).


%------------------------------------------------------------------------------
