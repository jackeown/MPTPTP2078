%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1074+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:50 EST 2020

% Result     : Theorem 1.22s
% Output     : CNFRefutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 280 expanded)
%              Number of clauses        :   47 (  72 expanded)
%              Number of leaves         :    9 (  87 expanded)
%              Depth                    :   17
%              Number of atoms          :  289 (1854 expanded)
%              Number of equality atoms :   56 (  76 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f14])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f12])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
              | ~ m1_subset_1(X4,X1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
     => ( ~ r1_tarski(k2_relset_1(X1,X2,sK5),X0)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(X1,X2,sK5,X4),X0)
            | ~ m1_subset_1(X4,X1) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK5,X1,X2)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(X1,sK4,X3),X0)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(X1,sK4,X3,X4),X0)
                | ~ m1_subset_1(X4,X1) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK4)))
            & v1_funct_2(X3,X1,sK4)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
                & ! [X4] :
                    ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                    | ~ m1_subset_1(X4,X1) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(sK3,X2,X3),sK2)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK3,X2,X3,X4),sK2)
                  | ~ m1_subset_1(X4,sK3) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X2)))
              & v1_funct_2(X3,sK3,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2)
        | ~ m1_subset_1(X4,sK3) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f13,f20,f19,f18])).

fof(f33,plain,(
    ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X0
          & m1_subset_1(X4,X1) )
      | ~ r2_hidden(X0,k2_relset_1(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X0
          & m1_subset_1(X4,X1) )
      | ~ r2_hidden(X0,k2_relset_1(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f16,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X0
          & m1_subset_1(X4,X1) )
     => ( k1_funct_1(X3,sK1(X0,X1,X3)) = X0
        & m1_subset_1(sK1(X0,X1,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_funct_1(X3,sK1(X0,X1,X3)) = X0
        & m1_subset_1(sK1(X0,X1,X3),X1) )
      | ~ r2_hidden(X0,k2_relset_1(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f16])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK1(X0,X1,X3),X1)
      | ~ r2_hidden(X0,k2_relset_1(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f29,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f27,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X3,sK1(X0,X1,X3)) = X0
      | ~ r2_hidden(X0,k2_relset_1(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK3,sK4,sK5,X4),sK2)
      | ~ m1_subset_1(X4,sK3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_137,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k2_relset_1(sK3,sK4,sK5) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_138,plain,
    ( r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),k2_relset_1(sK3,sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_137])).

cnf(c_516,plain,
    ( r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),k2_relset_1(sK3,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_138])).

cnf(c_725,plain,
    ( r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK1(X3,X1,X0),X1)
    | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_8,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_209,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK1(X3,X1,X0),X1)
    | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_210,plain,
    ( m1_subset_1(sK1(X0,sK3,sK5),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5))
    | ~ v1_funct_1(sK5) ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_9,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_214,plain,
    ( ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5))
    | m1_subset_1(sK1(X0,sK3,sK5),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_210,c_9,c_7])).

cnf(c_215,plain,
    ( m1_subset_1(sK1(X0,sK3,sK5),sK3)
    | ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5)) ),
    inference(renaming,[status(thm)],[c_214])).

cnf(c_514,plain,
    ( m1_subset_1(sK1(X0_47,sK3,sK5),sK3)
    | ~ r2_hidden(X0_47,k2_relset_1(sK3,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_215])).

cnf(c_727,plain,
    ( m1_subset_1(sK1(X0_47,sK3,sK5),sK3) = iProver_top
    | r2_hidden(X0_47,k2_relset_1(sK3,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_855,plain,
    ( m1_subset_1(sK1(sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK3,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_725,c_727])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_11,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_176,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_177,plain,
    ( ~ v1_funct_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ m1_subset_1(X2,sK3)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK3,X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_176])).

cnf(c_269,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ m1_subset_1(X2,sK3)
    | ~ v1_funct_1(X0)
    | k3_funct_2(sK3,X1,X0,X2) = k1_funct_1(X0,X2)
    | sK5 != X0
    | sK4 != X1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_177])).

cnf(c_270,plain,
    ( ~ m1_subset_1(X0,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK5)
    | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_269])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,sK3)
    | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_270,c_9,c_7])).

cnf(c_511,plain,
    ( ~ m1_subset_1(X0_45,sK3)
    | k3_funct_2(sK3,sK4,sK5,X0_45) = k1_funct_1(sK5,X0_45) ),
    inference(subtyping,[status(esa)],[c_274])).

cnf(c_731,plain,
    ( k3_funct_2(sK3,sK4,sK5,X0_45) = k1_funct_1(sK5,X0_45)
    | m1_subset_1(X0_45,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_960,plain,
    ( k3_funct_2(sK3,sK4,sK5,sK1(sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK3,sK5)) = k1_funct_1(sK5,sK1(sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_855,c_731])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK1(X3,X1,X0)) = X3 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_227,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK1(X3,X1,X0)) = X3
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_228,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5))
    | ~ v1_funct_1(sK5)
    | k1_funct_1(sK5,sK1(X0,sK3,sK5)) = X0 ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_232,plain,
    ( ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5))
    | k1_funct_1(sK5,sK1(X0,sK3,sK5)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_228,c_9,c_7])).

cnf(c_513,plain,
    ( ~ r2_hidden(X0_47,k2_relset_1(sK3,sK4,sK5))
    | k1_funct_1(sK5,sK1(X0_47,sK3,sK5)) = X0_47 ),
    inference(subtyping,[status(esa)],[c_232])).

cnf(c_728,plain,
    ( k1_funct_1(sK5,sK1(X0_47,sK3,sK5)) = X0_47
    | r2_hidden(X0_47,k2_relset_1(sK3,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_891,plain,
    ( k1_funct_1(sK5,sK1(sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK3,sK5)) = sK0(k2_relset_1(sK3,sK4,sK5),sK2) ),
    inference(superposition,[status(thm)],[c_725,c_728])).

cnf(c_1022,plain,
    ( k3_funct_2(sK3,sK4,sK5,sK1(sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK3,sK5)) = sK0(k2_relset_1(sK3,sK4,sK5),sK2) ),
    inference(light_normalisation,[status(thm)],[c_960,c_891])).

cnf(c_6,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | r2_hidden(k3_funct_2(sK3,sK4,sK5,X0),sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_518,negated_conjecture,
    ( ~ m1_subset_1(X0_45,sK3)
    | r2_hidden(k3_funct_2(sK3,sK4,sK5,X0_45),sK2) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_723,plain,
    ( m1_subset_1(X0_45,sK3) != iProver_top
    | r2_hidden(k3_funct_2(sK3,sK4,sK5,X0_45),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_1024,plain,
    ( m1_subset_1(sK1(sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK3,sK5),sK3) != iProver_top
    | r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1022,c_723])).

cnf(c_357,plain,
    ( m1_subset_1(sK1(X0,sK3,sK5),sK3)
    | k2_relset_1(sK3,sK4,sK5) != k2_relset_1(sK3,sK4,sK5)
    | sK0(k2_relset_1(sK3,sK4,sK5),sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_138,c_215])).

cnf(c_358,plain,
    ( m1_subset_1(sK1(sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK3,sK5),sK3) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_359,plain,
    ( m1_subset_1(sK1(sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK3,sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_144,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k2_relset_1(sK3,sK4,sK5) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_145,plain,
    ( ~ r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK2) ),
    inference(unflattening,[status(thm)],[c_144])).

cnf(c_146,plain,
    ( r2_hidden(sK0(k2_relset_1(sK3,sK4,sK5),sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_145])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1024,c_359,c_146])).


%------------------------------------------------------------------------------
