%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0598+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:41 EST 2020

% Result     : Theorem 0.67s
% Output     : CNFRefutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 112 expanded)
%              Number of clauses        :   22 (  31 expanded)
%              Number of leaves         :    8 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  135 ( 367 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( r2_hidden(X2,k2_relat_1(X1))
           => r2_hidden(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,k2_relat_1(X1)) )
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,k2_relat_1(X1)) )
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,k2_relat_1(X1)) )
     => ( ~ r2_hidden(sK2,X0)
        & r2_hidden(sK2,k2_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,k2_relat_1(X1)) )
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(X2,sK0)
          & r2_hidden(X2,k2_relat_1(sK1)) )
      & v5_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ~ r2_hidden(sK2,sK0)
    & r2_hidden(sK2,k2_relat_1(sK1))
    & v5_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f19,f18])).

fof(f30,plain,(
    r2_hidden(sK2,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f29,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_625,plain,
    ( m1_subset_1(X0_39,X1_39)
    | ~ m1_subset_1(X2_39,k1_zfmisc_1(X1_39))
    | ~ r2_hidden(X0_39,X2_39) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_662,plain,
    ( ~ m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(X0_39))
    | m1_subset_1(sK2,X0_39)
    | ~ r2_hidden(sK2,k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_664,plain,
    ( ~ m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0))
    | m1_subset_1(sK2,sK0)
    | ~ r2_hidden(sK2,k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_8,negated_conjecture,
    ( r2_hidden(sK2,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_84,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_85,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_84])).

cnf(c_109,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_85])).

cnf(c_9,negated_conjecture,
    ( v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_145,plain,
    ( r1_tarski(k2_relat_1(sK1),X0)
    | ~ v5_relat_1(sK1,X0) ),
    inference(resolution,[status(thm)],[c_1,c_10])).

cnf(c_174,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(resolution,[status(thm)],[c_9,c_145])).

cnf(c_220,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK1))
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[status(thm)],[c_109,c_174])).

cnf(c_351,plain,
    ( ~ v1_xboole_0(sK0) ),
    inference(resolution,[status(thm)],[c_8,c_220])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_7,negated_conjecture,
    ( ~ r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_306,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[status(thm)],[c_2,c_7])).

cnf(c_214,plain,
    ( m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[status(thm)],[c_85,c_174])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_664,c_351,c_306,c_214,c_8])).


%------------------------------------------------------------------------------
