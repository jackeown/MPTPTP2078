%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:12 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 292 expanded)
%              Number of clauses        :   73 ( 106 expanded)
%              Number of leaves         :   20 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  419 (1194 expanded)
%              Number of equality atoms :  127 ( 216 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f45,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
        | ~ v1_funct_1(sK2) )
      & r1_tarski(k2_relat_1(sK2),sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
      | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
      | ~ v1_funct_1(sK2) )
    & r1_tarski(k2_relat_1(sK2),sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f45])).

fof(f77,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f64,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f84,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f71])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1912,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_705,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1530,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) != X0
    | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_1731,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) != k1_relat_1(sK2)
    | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1530])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1496,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | k1_relset_1(X0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1498,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_24,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_27,negated_conjecture,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_166,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_29])).

cnf(c_167,negated_conjecture,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(renaming,[status(thm)],[c_166])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK2) != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_167])).

cnf(c_514,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_relset_1(k1_relat_1(sK2),sK1,sK2) != k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_522,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_xboole_0 = sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_514,c_19])).

cnf(c_1141,plain,
    ( k1_xboole_0 = sK1
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_20,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_424,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_425,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k2_relat_1(sK2),X1)
    | ~ r1_tarski(k1_relat_1(sK2),X0) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_1279,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r1_tarski(k1_relat_1(sK2),X0) ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_1365,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1279])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1366,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1415,plain,
    ( k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1141,c_28,c_522,c_1365,c_1366])).

cnf(c_1148,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1420,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1415,c_1148])).

cnf(c_17,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1407,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1408,plain,
    ( v1_xboole_0(k1_relat_1(sK2)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1407])).

cnf(c_707,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1402,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(sK2))
    | k1_relat_1(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_1404,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_708,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1371,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK2),X2)
    | X2 != X1
    | k1_relat_1(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_1373,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK2) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1371])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1339,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1340,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | v1_xboole_0(k1_relat_1(sK2)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1339])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_235,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_236,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_235])).

cnf(c_289,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_15,c_236])).

cnf(c_405,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | sK0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_289])).

cnf(c_406,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_1303,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_1304,plain,
    ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1303])).

cnf(c_1306,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top
    | v1_xboole_0(k2_relat_1(sK2)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_1281,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1279])).

cnf(c_23,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_167])).

cnf(c_498,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_439,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_440,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_441,plain,
    ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_440])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_87,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_89,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_88,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_85,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_83,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_80,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_82,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_81,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1912,c_1731,c_1498,c_1420,c_1408,c_1404,c_1373,c_1366,c_1365,c_1340,c_1306,c_1281,c_498,c_441,c_89,c_88,c_85,c_83,c_10,c_82,c_81,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:19:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.75/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/0.97  
% 1.75/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.75/0.97  
% 1.75/0.97  ------  iProver source info
% 1.75/0.97  
% 1.75/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.75/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.75/0.97  git: non_committed_changes: false
% 1.75/0.97  git: last_make_outside_of_git: false
% 1.75/0.97  
% 1.75/0.97  ------ 
% 1.75/0.97  
% 1.75/0.97  ------ Input Options
% 1.75/0.97  
% 1.75/0.97  --out_options                           all
% 1.75/0.97  --tptp_safe_out                         true
% 1.75/0.97  --problem_path                          ""
% 1.75/0.97  --include_path                          ""
% 1.75/0.97  --clausifier                            res/vclausify_rel
% 1.75/0.97  --clausifier_options                    --mode clausify
% 1.75/0.97  --stdin                                 false
% 1.75/0.97  --stats_out                             all
% 1.75/0.97  
% 1.75/0.97  ------ General Options
% 1.75/0.97  
% 1.75/0.97  --fof                                   false
% 1.75/0.97  --time_out_real                         305.
% 1.75/0.97  --time_out_virtual                      -1.
% 1.75/0.97  --symbol_type_check                     false
% 1.75/0.97  --clausify_out                          false
% 1.75/0.97  --sig_cnt_out                           false
% 1.75/0.97  --trig_cnt_out                          false
% 1.75/0.97  --trig_cnt_out_tolerance                1.
% 1.75/0.97  --trig_cnt_out_sk_spl                   false
% 1.75/0.97  --abstr_cl_out                          false
% 1.75/0.97  
% 1.75/0.97  ------ Global Options
% 1.75/0.97  
% 1.75/0.97  --schedule                              default
% 1.75/0.97  --add_important_lit                     false
% 1.75/0.97  --prop_solver_per_cl                    1000
% 1.75/0.97  --min_unsat_core                        false
% 1.75/0.97  --soft_assumptions                      false
% 1.75/0.97  --soft_lemma_size                       3
% 1.75/0.97  --prop_impl_unit_size                   0
% 1.75/0.97  --prop_impl_unit                        []
% 1.75/0.97  --share_sel_clauses                     true
% 1.75/0.97  --reset_solvers                         false
% 1.75/0.97  --bc_imp_inh                            [conj_cone]
% 1.75/0.97  --conj_cone_tolerance                   3.
% 1.75/0.97  --extra_neg_conj                        none
% 1.75/0.97  --large_theory_mode                     true
% 1.75/0.97  --prolific_symb_bound                   200
% 1.75/0.97  --lt_threshold                          2000
% 1.75/0.97  --clause_weak_htbl                      true
% 1.75/0.97  --gc_record_bc_elim                     false
% 1.75/0.97  
% 1.75/0.97  ------ Preprocessing Options
% 1.75/0.97  
% 1.75/0.97  --preprocessing_flag                    true
% 1.75/0.97  --time_out_prep_mult                    0.1
% 1.75/0.97  --splitting_mode                        input
% 1.75/0.97  --splitting_grd                         true
% 1.75/0.97  --splitting_cvd                         false
% 1.75/0.97  --splitting_cvd_svl                     false
% 1.75/0.97  --splitting_nvd                         32
% 1.75/0.97  --sub_typing                            true
% 1.75/0.97  --prep_gs_sim                           true
% 1.75/0.97  --prep_unflatten                        true
% 1.75/0.97  --prep_res_sim                          true
% 1.75/0.97  --prep_upred                            true
% 1.75/0.97  --prep_sem_filter                       exhaustive
% 1.75/0.97  --prep_sem_filter_out                   false
% 1.75/0.97  --pred_elim                             true
% 1.75/0.97  --res_sim_input                         true
% 1.75/0.97  --eq_ax_congr_red                       true
% 1.75/0.97  --pure_diseq_elim                       true
% 1.75/0.97  --brand_transform                       false
% 1.75/0.97  --non_eq_to_eq                          false
% 1.75/0.97  --prep_def_merge                        true
% 1.75/0.97  --prep_def_merge_prop_impl              false
% 1.75/0.97  --prep_def_merge_mbd                    true
% 1.75/0.97  --prep_def_merge_tr_red                 false
% 1.75/0.97  --prep_def_merge_tr_cl                  false
% 1.75/0.97  --smt_preprocessing                     true
% 1.75/0.97  --smt_ac_axioms                         fast
% 1.75/0.97  --preprocessed_out                      false
% 1.75/0.97  --preprocessed_stats                    false
% 1.75/0.97  
% 1.75/0.97  ------ Abstraction refinement Options
% 1.75/0.97  
% 1.75/0.97  --abstr_ref                             []
% 1.75/0.97  --abstr_ref_prep                        false
% 1.75/0.97  --abstr_ref_until_sat                   false
% 1.75/0.97  --abstr_ref_sig_restrict                funpre
% 1.75/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.75/0.97  --abstr_ref_under                       []
% 1.75/0.97  
% 1.75/0.97  ------ SAT Options
% 1.75/0.97  
% 1.75/0.97  --sat_mode                              false
% 1.75/0.97  --sat_fm_restart_options                ""
% 1.75/0.97  --sat_gr_def                            false
% 1.75/0.97  --sat_epr_types                         true
% 1.75/0.97  --sat_non_cyclic_types                  false
% 1.75/0.97  --sat_finite_models                     false
% 1.75/0.97  --sat_fm_lemmas                         false
% 1.75/0.97  --sat_fm_prep                           false
% 1.75/0.97  --sat_fm_uc_incr                        true
% 1.75/0.97  --sat_out_model                         small
% 1.75/0.97  --sat_out_clauses                       false
% 1.75/0.97  
% 1.75/0.97  ------ QBF Options
% 1.75/0.97  
% 1.75/0.97  --qbf_mode                              false
% 1.75/0.97  --qbf_elim_univ                         false
% 1.75/0.97  --qbf_dom_inst                          none
% 1.75/0.97  --qbf_dom_pre_inst                      false
% 1.75/0.97  --qbf_sk_in                             false
% 1.75/0.97  --qbf_pred_elim                         true
% 1.75/0.97  --qbf_split                             512
% 1.75/0.97  
% 1.75/0.97  ------ BMC1 Options
% 1.75/0.97  
% 1.75/0.97  --bmc1_incremental                      false
% 1.75/0.97  --bmc1_axioms                           reachable_all
% 1.75/0.97  --bmc1_min_bound                        0
% 1.75/0.97  --bmc1_max_bound                        -1
% 1.75/0.97  --bmc1_max_bound_default                -1
% 1.75/0.97  --bmc1_symbol_reachability              true
% 1.75/0.97  --bmc1_property_lemmas                  false
% 1.75/0.97  --bmc1_k_induction                      false
% 1.75/0.97  --bmc1_non_equiv_states                 false
% 1.75/0.97  --bmc1_deadlock                         false
% 1.75/0.97  --bmc1_ucm                              false
% 1.75/0.97  --bmc1_add_unsat_core                   none
% 1.75/0.97  --bmc1_unsat_core_children              false
% 1.75/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.75/0.97  --bmc1_out_stat                         full
% 1.75/0.97  --bmc1_ground_init                      false
% 1.75/0.97  --bmc1_pre_inst_next_state              false
% 1.75/0.97  --bmc1_pre_inst_state                   false
% 1.75/0.97  --bmc1_pre_inst_reach_state             false
% 1.75/0.97  --bmc1_out_unsat_core                   false
% 1.75/0.97  --bmc1_aig_witness_out                  false
% 1.75/0.97  --bmc1_verbose                          false
% 1.75/0.97  --bmc1_dump_clauses_tptp                false
% 1.75/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.75/0.97  --bmc1_dump_file                        -
% 1.75/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.75/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.75/0.97  --bmc1_ucm_extend_mode                  1
% 1.75/0.97  --bmc1_ucm_init_mode                    2
% 1.75/0.97  --bmc1_ucm_cone_mode                    none
% 1.75/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.75/0.97  --bmc1_ucm_relax_model                  4
% 1.75/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.75/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.75/0.97  --bmc1_ucm_layered_model                none
% 1.75/0.97  --bmc1_ucm_max_lemma_size               10
% 1.75/0.97  
% 1.75/0.97  ------ AIG Options
% 1.75/0.97  
% 1.75/0.97  --aig_mode                              false
% 1.75/0.97  
% 1.75/0.97  ------ Instantiation Options
% 1.75/0.97  
% 1.75/0.97  --instantiation_flag                    true
% 1.75/0.97  --inst_sos_flag                         false
% 1.75/0.97  --inst_sos_phase                        true
% 1.75/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.75/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.75/0.97  --inst_lit_sel_side                     num_symb
% 1.75/0.97  --inst_solver_per_active                1400
% 1.75/0.97  --inst_solver_calls_frac                1.
% 1.75/0.97  --inst_passive_queue_type               priority_queues
% 1.75/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.75/0.97  --inst_passive_queues_freq              [25;2]
% 1.75/0.97  --inst_dismatching                      true
% 1.75/0.97  --inst_eager_unprocessed_to_passive     true
% 1.75/0.97  --inst_prop_sim_given                   true
% 1.75/0.97  --inst_prop_sim_new                     false
% 1.75/0.97  --inst_subs_new                         false
% 1.75/0.97  --inst_eq_res_simp                      false
% 1.75/0.97  --inst_subs_given                       false
% 1.75/0.97  --inst_orphan_elimination               true
% 1.75/0.97  --inst_learning_loop_flag               true
% 1.75/0.97  --inst_learning_start                   3000
% 1.75/0.97  --inst_learning_factor                  2
% 1.75/0.97  --inst_start_prop_sim_after_learn       3
% 1.75/0.97  --inst_sel_renew                        solver
% 1.75/0.97  --inst_lit_activity_flag                true
% 1.75/0.97  --inst_restr_to_given                   false
% 1.75/0.97  --inst_activity_threshold               500
% 1.75/0.97  --inst_out_proof                        true
% 1.75/0.97  
% 1.75/0.97  ------ Resolution Options
% 1.75/0.97  
% 1.75/0.97  --resolution_flag                       true
% 1.75/0.97  --res_lit_sel                           adaptive
% 1.75/0.97  --res_lit_sel_side                      none
% 1.75/0.97  --res_ordering                          kbo
% 1.75/0.97  --res_to_prop_solver                    active
% 1.75/0.97  --res_prop_simpl_new                    false
% 1.75/0.97  --res_prop_simpl_given                  true
% 1.75/0.97  --res_passive_queue_type                priority_queues
% 1.75/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.75/0.97  --res_passive_queues_freq               [15;5]
% 1.75/0.97  --res_forward_subs                      full
% 1.75/0.97  --res_backward_subs                     full
% 1.75/0.97  --res_forward_subs_resolution           true
% 1.75/0.97  --res_backward_subs_resolution          true
% 1.75/0.97  --res_orphan_elimination                true
% 1.75/0.97  --res_time_limit                        2.
% 1.75/0.97  --res_out_proof                         true
% 1.75/0.97  
% 1.75/0.97  ------ Superposition Options
% 1.75/0.97  
% 1.75/0.97  --superposition_flag                    true
% 1.75/0.97  --sup_passive_queue_type                priority_queues
% 1.75/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.75/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.75/0.97  --demod_completeness_check              fast
% 1.75/0.97  --demod_use_ground                      true
% 1.75/0.97  --sup_to_prop_solver                    passive
% 1.75/0.97  --sup_prop_simpl_new                    true
% 1.75/0.97  --sup_prop_simpl_given                  true
% 1.75/0.97  --sup_fun_splitting                     false
% 1.75/0.97  --sup_smt_interval                      50000
% 1.75/0.97  
% 1.75/0.97  ------ Superposition Simplification Setup
% 1.75/0.97  
% 1.75/0.97  --sup_indices_passive                   []
% 1.75/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.75/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.97  --sup_full_bw                           [BwDemod]
% 1.75/0.97  --sup_immed_triv                        [TrivRules]
% 1.75/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.75/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.97  --sup_immed_bw_main                     []
% 1.75/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.75/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.75/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.75/0.97  
% 1.75/0.97  ------ Combination Options
% 1.75/0.97  
% 1.75/0.97  --comb_res_mult                         3
% 1.75/0.97  --comb_sup_mult                         2
% 1.75/0.97  --comb_inst_mult                        10
% 1.75/0.97  
% 1.75/0.97  ------ Debug Options
% 1.75/0.97  
% 1.75/0.97  --dbg_backtrace                         false
% 1.75/0.97  --dbg_dump_prop_clauses                 false
% 1.75/0.97  --dbg_dump_prop_clauses_file            -
% 1.75/0.97  --dbg_out_stat                          false
% 1.75/0.97  ------ Parsing...
% 1.75/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.75/0.97  
% 1.75/0.97  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.75/0.97  
% 1.75/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.75/0.97  
% 1.75/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.75/0.97  ------ Proving...
% 1.75/0.97  ------ Problem Properties 
% 1.75/0.97  
% 1.75/0.97  
% 1.75/0.97  clauses                                 20
% 1.75/0.97  conjectures                             1
% 1.75/0.97  EPR                                     7
% 1.75/0.97  Horn                                    20
% 1.75/0.97  unary                                   7
% 1.75/0.97  binary                                  7
% 1.75/0.97  lits                                    42
% 1.75/0.97  lits eq                                 13
% 1.75/0.97  fd_pure                                 0
% 1.75/0.97  fd_pseudo                               0
% 1.75/0.97  fd_cond                                 1
% 1.75/0.97  fd_pseudo_cond                          2
% 1.75/0.97  AC symbols                              0
% 1.75/0.97  
% 1.75/0.97  ------ Schedule dynamic 5 is on 
% 1.75/0.97  
% 1.75/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.75/0.97  
% 1.75/0.97  
% 1.75/0.97  ------ 
% 1.75/0.97  Current options:
% 1.75/0.97  ------ 
% 1.75/0.97  
% 1.75/0.97  ------ Input Options
% 1.75/0.97  
% 1.75/0.97  --out_options                           all
% 1.75/0.97  --tptp_safe_out                         true
% 1.75/0.97  --problem_path                          ""
% 1.75/0.97  --include_path                          ""
% 1.75/0.97  --clausifier                            res/vclausify_rel
% 1.75/0.97  --clausifier_options                    --mode clausify
% 1.75/0.97  --stdin                                 false
% 1.75/0.97  --stats_out                             all
% 1.75/0.97  
% 1.75/0.97  ------ General Options
% 1.75/0.97  
% 1.75/0.97  --fof                                   false
% 1.75/0.97  --time_out_real                         305.
% 1.75/0.97  --time_out_virtual                      -1.
% 1.75/0.97  --symbol_type_check                     false
% 1.75/0.97  --clausify_out                          false
% 1.75/0.97  --sig_cnt_out                           false
% 1.75/0.97  --trig_cnt_out                          false
% 1.75/0.97  --trig_cnt_out_tolerance                1.
% 1.75/0.97  --trig_cnt_out_sk_spl                   false
% 1.75/0.97  --abstr_cl_out                          false
% 1.75/0.97  
% 1.75/0.97  ------ Global Options
% 1.75/0.97  
% 1.75/0.97  --schedule                              default
% 1.75/0.97  --add_important_lit                     false
% 1.75/0.97  --prop_solver_per_cl                    1000
% 1.75/0.97  --min_unsat_core                        false
% 1.75/0.97  --soft_assumptions                      false
% 1.75/0.97  --soft_lemma_size                       3
% 1.75/0.97  --prop_impl_unit_size                   0
% 1.75/0.97  --prop_impl_unit                        []
% 1.75/0.97  --share_sel_clauses                     true
% 1.75/0.97  --reset_solvers                         false
% 1.75/0.97  --bc_imp_inh                            [conj_cone]
% 1.75/0.97  --conj_cone_tolerance                   3.
% 1.75/0.97  --extra_neg_conj                        none
% 1.75/0.97  --large_theory_mode                     true
% 1.75/0.97  --prolific_symb_bound                   200
% 1.75/0.97  --lt_threshold                          2000
% 1.75/0.97  --clause_weak_htbl                      true
% 1.75/0.97  --gc_record_bc_elim                     false
% 1.75/0.97  
% 1.75/0.97  ------ Preprocessing Options
% 1.75/0.97  
% 1.75/0.97  --preprocessing_flag                    true
% 1.75/0.97  --time_out_prep_mult                    0.1
% 1.75/0.97  --splitting_mode                        input
% 1.75/0.97  --splitting_grd                         true
% 1.75/0.97  --splitting_cvd                         false
% 1.75/0.97  --splitting_cvd_svl                     false
% 1.75/0.97  --splitting_nvd                         32
% 1.75/0.97  --sub_typing                            true
% 1.75/0.97  --prep_gs_sim                           true
% 1.75/0.97  --prep_unflatten                        true
% 1.75/0.97  --prep_res_sim                          true
% 1.75/0.97  --prep_upred                            true
% 1.75/0.97  --prep_sem_filter                       exhaustive
% 1.75/0.97  --prep_sem_filter_out                   false
% 1.75/0.97  --pred_elim                             true
% 1.75/0.97  --res_sim_input                         true
% 1.75/0.97  --eq_ax_congr_red                       true
% 1.75/0.97  --pure_diseq_elim                       true
% 1.75/0.97  --brand_transform                       false
% 1.75/0.97  --non_eq_to_eq                          false
% 1.75/0.97  --prep_def_merge                        true
% 1.75/0.97  --prep_def_merge_prop_impl              false
% 1.75/0.97  --prep_def_merge_mbd                    true
% 1.75/0.97  --prep_def_merge_tr_red                 false
% 1.75/0.97  --prep_def_merge_tr_cl                  false
% 1.75/0.97  --smt_preprocessing                     true
% 1.75/0.97  --smt_ac_axioms                         fast
% 1.75/0.97  --preprocessed_out                      false
% 1.75/0.97  --preprocessed_stats                    false
% 1.75/0.97  
% 1.75/0.97  ------ Abstraction refinement Options
% 1.75/0.97  
% 1.75/0.97  --abstr_ref                             []
% 1.75/0.97  --abstr_ref_prep                        false
% 1.75/0.97  --abstr_ref_until_sat                   false
% 1.75/0.97  --abstr_ref_sig_restrict                funpre
% 1.75/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.75/0.97  --abstr_ref_under                       []
% 1.75/0.97  
% 1.75/0.97  ------ SAT Options
% 1.75/0.97  
% 1.75/0.97  --sat_mode                              false
% 1.75/0.97  --sat_fm_restart_options                ""
% 1.75/0.97  --sat_gr_def                            false
% 1.75/0.97  --sat_epr_types                         true
% 1.75/0.97  --sat_non_cyclic_types                  false
% 1.75/0.97  --sat_finite_models                     false
% 1.75/0.97  --sat_fm_lemmas                         false
% 1.75/0.97  --sat_fm_prep                           false
% 1.75/0.97  --sat_fm_uc_incr                        true
% 1.75/0.97  --sat_out_model                         small
% 1.75/0.97  --sat_out_clauses                       false
% 1.75/0.97  
% 1.75/0.97  ------ QBF Options
% 1.75/0.97  
% 1.75/0.97  --qbf_mode                              false
% 1.75/0.97  --qbf_elim_univ                         false
% 1.75/0.97  --qbf_dom_inst                          none
% 1.75/0.97  --qbf_dom_pre_inst                      false
% 1.75/0.97  --qbf_sk_in                             false
% 1.75/0.97  --qbf_pred_elim                         true
% 1.75/0.97  --qbf_split                             512
% 1.75/0.97  
% 1.75/0.97  ------ BMC1 Options
% 1.75/0.97  
% 1.75/0.97  --bmc1_incremental                      false
% 1.75/0.97  --bmc1_axioms                           reachable_all
% 1.75/0.97  --bmc1_min_bound                        0
% 1.75/0.97  --bmc1_max_bound                        -1
% 1.75/0.97  --bmc1_max_bound_default                -1
% 1.75/0.98  --bmc1_symbol_reachability              true
% 1.75/0.98  --bmc1_property_lemmas                  false
% 1.75/0.98  --bmc1_k_induction                      false
% 1.75/0.98  --bmc1_non_equiv_states                 false
% 1.75/0.98  --bmc1_deadlock                         false
% 1.75/0.98  --bmc1_ucm                              false
% 1.75/0.98  --bmc1_add_unsat_core                   none
% 1.75/0.98  --bmc1_unsat_core_children              false
% 1.75/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.75/0.98  --bmc1_out_stat                         full
% 1.75/0.98  --bmc1_ground_init                      false
% 1.75/0.98  --bmc1_pre_inst_next_state              false
% 1.75/0.98  --bmc1_pre_inst_state                   false
% 1.75/0.98  --bmc1_pre_inst_reach_state             false
% 1.75/0.98  --bmc1_out_unsat_core                   false
% 1.75/0.98  --bmc1_aig_witness_out                  false
% 1.75/0.98  --bmc1_verbose                          false
% 1.75/0.98  --bmc1_dump_clauses_tptp                false
% 1.75/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.75/0.98  --bmc1_dump_file                        -
% 1.75/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.75/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.75/0.98  --bmc1_ucm_extend_mode                  1
% 1.75/0.98  --bmc1_ucm_init_mode                    2
% 1.75/0.98  --bmc1_ucm_cone_mode                    none
% 1.75/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.75/0.98  --bmc1_ucm_relax_model                  4
% 1.75/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.75/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.75/0.98  --bmc1_ucm_layered_model                none
% 1.75/0.98  --bmc1_ucm_max_lemma_size               10
% 1.75/0.98  
% 1.75/0.98  ------ AIG Options
% 1.75/0.98  
% 1.75/0.98  --aig_mode                              false
% 1.75/0.98  
% 1.75/0.98  ------ Instantiation Options
% 1.75/0.98  
% 1.75/0.98  --instantiation_flag                    true
% 1.75/0.98  --inst_sos_flag                         false
% 1.75/0.98  --inst_sos_phase                        true
% 1.75/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.75/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.75/0.98  --inst_lit_sel_side                     none
% 1.75/0.98  --inst_solver_per_active                1400
% 1.75/0.98  --inst_solver_calls_frac                1.
% 1.75/0.98  --inst_passive_queue_type               priority_queues
% 1.75/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.75/0.98  --inst_passive_queues_freq              [25;2]
% 1.75/0.98  --inst_dismatching                      true
% 1.75/0.98  --inst_eager_unprocessed_to_passive     true
% 1.75/0.98  --inst_prop_sim_given                   true
% 1.75/0.98  --inst_prop_sim_new                     false
% 1.75/0.98  --inst_subs_new                         false
% 1.75/0.98  --inst_eq_res_simp                      false
% 1.75/0.98  --inst_subs_given                       false
% 1.75/0.98  --inst_orphan_elimination               true
% 1.75/0.98  --inst_learning_loop_flag               true
% 1.75/0.98  --inst_learning_start                   3000
% 1.75/0.98  --inst_learning_factor                  2
% 1.75/0.98  --inst_start_prop_sim_after_learn       3
% 1.75/0.98  --inst_sel_renew                        solver
% 1.75/0.98  --inst_lit_activity_flag                true
% 1.75/0.98  --inst_restr_to_given                   false
% 1.75/0.98  --inst_activity_threshold               500
% 1.75/0.98  --inst_out_proof                        true
% 1.75/0.98  
% 1.75/0.98  ------ Resolution Options
% 1.75/0.98  
% 1.75/0.98  --resolution_flag                       false
% 1.75/0.98  --res_lit_sel                           adaptive
% 1.75/0.98  --res_lit_sel_side                      none
% 1.75/0.98  --res_ordering                          kbo
% 1.75/0.98  --res_to_prop_solver                    active
% 1.75/0.98  --res_prop_simpl_new                    false
% 1.75/0.98  --res_prop_simpl_given                  true
% 1.75/0.98  --res_passive_queue_type                priority_queues
% 1.75/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.75/0.98  --res_passive_queues_freq               [15;5]
% 1.75/0.98  --res_forward_subs                      full
% 1.75/0.98  --res_backward_subs                     full
% 1.75/0.98  --res_forward_subs_resolution           true
% 1.75/0.98  --res_backward_subs_resolution          true
% 1.75/0.98  --res_orphan_elimination                true
% 1.75/0.98  --res_time_limit                        2.
% 1.75/0.98  --res_out_proof                         true
% 1.75/0.98  
% 1.75/0.98  ------ Superposition Options
% 1.75/0.98  
% 1.75/0.98  --superposition_flag                    true
% 1.75/0.98  --sup_passive_queue_type                priority_queues
% 1.75/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.75/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.75/0.98  --demod_completeness_check              fast
% 1.75/0.98  --demod_use_ground                      true
% 1.75/0.98  --sup_to_prop_solver                    passive
% 1.75/0.98  --sup_prop_simpl_new                    true
% 1.75/0.98  --sup_prop_simpl_given                  true
% 1.75/0.98  --sup_fun_splitting                     false
% 1.75/0.98  --sup_smt_interval                      50000
% 1.75/0.98  
% 1.75/0.98  ------ Superposition Simplification Setup
% 1.75/0.98  
% 1.75/0.98  --sup_indices_passive                   []
% 1.75/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.75/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.75/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.98  --sup_full_bw                           [BwDemod]
% 1.75/0.98  --sup_immed_triv                        [TrivRules]
% 1.75/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.75/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.98  --sup_immed_bw_main                     []
% 1.75/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.75/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.75/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.75/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.75/0.98  
% 1.75/0.98  ------ Combination Options
% 1.75/0.98  
% 1.75/0.98  --comb_res_mult                         3
% 1.75/0.98  --comb_sup_mult                         2
% 1.75/0.98  --comb_inst_mult                        10
% 1.75/0.98  
% 1.75/0.98  ------ Debug Options
% 1.75/0.98  
% 1.75/0.98  --dbg_backtrace                         false
% 1.75/0.98  --dbg_dump_prop_clauses                 false
% 1.75/0.98  --dbg_dump_prop_clauses_file            -
% 1.75/0.98  --dbg_out_stat                          false
% 1.75/0.98  
% 1.75/0.98  
% 1.75/0.98  
% 1.75/0.98  
% 1.75/0.98  ------ Proving...
% 1.75/0.98  
% 1.75/0.98  
% 1.75/0.98  % SZS status Theorem for theBenchmark.p
% 1.75/0.98  
% 1.75/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.75/0.98  
% 1.75/0.98  fof(f3,axiom,(
% 1.75/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.98  
% 1.75/0.98  fof(f20,plain,(
% 1.75/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.75/0.98    inference(ennf_transformation,[],[f3])).
% 1.75/0.98  
% 1.75/0.98  fof(f50,plain,(
% 1.75/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.75/0.98    inference(cnf_transformation,[],[f20])).
% 1.75/0.98  
% 1.75/0.98  fof(f15,axiom,(
% 1.75/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.98  
% 1.75/0.98  fof(f30,plain,(
% 1.75/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.98    inference(ennf_transformation,[],[f15])).
% 1.75/0.98  
% 1.75/0.98  fof(f66,plain,(
% 1.75/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.75/0.98    inference(cnf_transformation,[],[f30])).
% 1.75/0.98  
% 1.75/0.98  fof(f17,axiom,(
% 1.75/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.98  
% 1.75/0.98  fof(f33,plain,(
% 1.75/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.98    inference(ennf_transformation,[],[f17])).
% 1.75/0.98  
% 1.75/0.98  fof(f34,plain,(
% 1.75/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.98    inference(flattening,[],[f33])).
% 1.75/0.98  
% 1.75/0.98  fof(f44,plain,(
% 1.75/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.98    inference(nnf_transformation,[],[f34])).
% 1.75/0.98  
% 1.75/0.98  fof(f70,plain,(
% 1.75/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.75/0.98    inference(cnf_transformation,[],[f44])).
% 1.75/0.98  
% 1.75/0.98  fof(f18,conjecture,(
% 1.75/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.98  
% 1.75/0.98  fof(f19,negated_conjecture,(
% 1.75/0.98    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.75/0.98    inference(negated_conjecture,[],[f18])).
% 1.75/0.98  
% 1.75/0.98  fof(f35,plain,(
% 1.75/0.98    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.75/0.98    inference(ennf_transformation,[],[f19])).
% 1.75/0.98  
% 1.75/0.98  fof(f36,plain,(
% 1.75/0.98    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.75/0.98    inference(flattening,[],[f35])).
% 1.75/0.98  
% 1.75/0.98  fof(f45,plain,(
% 1.75/0.98    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)) & r1_tarski(k2_relat_1(sK2),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.75/0.98    introduced(choice_axiom,[])).
% 1.75/0.98  
% 1.75/0.98  fof(f46,plain,(
% 1.75/0.98    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)) & r1_tarski(k2_relat_1(sK2),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f45])).
% 1.75/0.98  
% 1.75/0.98  fof(f77,plain,(
% 1.75/0.98    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)),
% 1.75/0.98    inference(cnf_transformation,[],[f46])).
% 1.75/0.98  
% 1.75/0.98  fof(f75,plain,(
% 1.75/0.98    v1_funct_1(sK2)),
% 1.75/0.98    inference(cnf_transformation,[],[f46])).
% 1.75/0.98  
% 1.75/0.98  fof(f76,plain,(
% 1.75/0.98    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.75/0.98    inference(cnf_transformation,[],[f46])).
% 1.75/0.98  
% 1.75/0.98  fof(f16,axiom,(
% 1.75/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.98  
% 1.75/0.98  fof(f31,plain,(
% 1.75/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.75/0.98    inference(ennf_transformation,[],[f16])).
% 1.75/0.98  
% 1.75/0.98  fof(f32,plain,(
% 1.75/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.75/0.98    inference(flattening,[],[f31])).
% 1.75/0.98  
% 1.75/0.98  fof(f67,plain,(
% 1.75/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.75/0.98    inference(cnf_transformation,[],[f32])).
% 1.75/0.98  
% 1.75/0.98  fof(f74,plain,(
% 1.75/0.98    v1_relat_1(sK2)),
% 1.75/0.98    inference(cnf_transformation,[],[f46])).
% 1.75/0.98  
% 1.75/0.98  fof(f4,axiom,(
% 1.75/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.98  
% 1.75/0.98  fof(f41,plain,(
% 1.75/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.75/0.98    inference(nnf_transformation,[],[f4])).
% 1.75/0.98  
% 1.75/0.98  fof(f42,plain,(
% 1.75/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.75/0.98    inference(flattening,[],[f41])).
% 1.75/0.98  
% 1.75/0.98  fof(f51,plain,(
% 1.75/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.75/0.98    inference(cnf_transformation,[],[f42])).
% 1.75/0.98  
% 1.75/0.98  fof(f79,plain,(
% 1.75/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.75/0.98    inference(equality_resolution,[],[f51])).
% 1.75/0.98  
% 1.75/0.98  fof(f13,axiom,(
% 1.75/0.98    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 1.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.98  
% 1.75/0.98  fof(f27,plain,(
% 1.75/0.98    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.75/0.98    inference(ennf_transformation,[],[f13])).
% 1.75/0.98  
% 1.75/0.98  fof(f64,plain,(
% 1.75/0.98    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.75/0.98    inference(cnf_transformation,[],[f27])).
% 1.75/0.98  
% 1.75/0.98  fof(f9,axiom,(
% 1.75/0.98    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.98  
% 1.75/0.98  fof(f24,plain,(
% 1.75/0.98    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.75/0.98    inference(ennf_transformation,[],[f9])).
% 1.75/0.98  
% 1.75/0.98  fof(f59,plain,(
% 1.75/0.98    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.75/0.98    inference(cnf_transformation,[],[f24])).
% 1.75/0.98  
% 1.75/0.98  fof(f2,axiom,(
% 1.75/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.98  
% 1.75/0.98  fof(f37,plain,(
% 1.75/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.75/0.98    inference(nnf_transformation,[],[f2])).
% 1.75/0.98  
% 1.75/0.98  fof(f38,plain,(
% 1.75/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.75/0.98    inference(rectify,[],[f37])).
% 1.75/0.98  
% 1.75/0.98  fof(f39,plain,(
% 1.75/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.75/0.98    introduced(choice_axiom,[])).
% 1.75/0.98  
% 1.75/0.98  fof(f40,plain,(
% 1.75/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 1.75/0.98  
% 1.75/0.98  fof(f49,plain,(
% 1.75/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.75/0.98    inference(cnf_transformation,[],[f40])).
% 1.75/0.98  
% 1.75/0.98  fof(f11,axiom,(
% 1.75/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.98  
% 1.75/0.98  fof(f25,plain,(
% 1.75/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.75/0.98    inference(ennf_transformation,[],[f11])).
% 1.75/0.98  
% 1.75/0.98  fof(f62,plain,(
% 1.75/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.75/0.98    inference(cnf_transformation,[],[f25])).
% 1.75/0.98  
% 1.75/0.98  fof(f10,axiom,(
% 1.75/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.98  
% 1.75/0.98  fof(f43,plain,(
% 1.75/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.75/0.98    inference(nnf_transformation,[],[f10])).
% 1.75/0.98  
% 1.75/0.98  fof(f61,plain,(
% 1.75/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.75/0.98    inference(cnf_transformation,[],[f43])).
% 1.75/0.98  
% 1.75/0.98  fof(f71,plain,(
% 1.75/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.75/0.98    inference(cnf_transformation,[],[f44])).
% 1.75/0.98  
% 1.75/0.98  fof(f84,plain,(
% 1.75/0.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.75/0.98    inference(equality_resolution,[],[f71])).
% 1.75/0.98  
% 1.75/0.98  fof(f14,axiom,(
% 1.75/0.98    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 1.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.98  
% 1.75/0.98  fof(f28,plain,(
% 1.75/0.98    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.75/0.98    inference(ennf_transformation,[],[f14])).
% 1.75/0.98  
% 1.75/0.98  fof(f29,plain,(
% 1.75/0.98    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.75/0.98    inference(flattening,[],[f28])).
% 1.75/0.98  
% 1.75/0.98  fof(f65,plain,(
% 1.75/0.98    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.75/0.98    inference(cnf_transformation,[],[f29])).
% 1.75/0.98  
% 1.75/0.98  fof(f6,axiom,(
% 1.75/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.75/0.98  
% 1.75/0.98  fof(f55,plain,(
% 1.75/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.75/0.98    inference(cnf_transformation,[],[f6])).
% 1.83/0.98  
% 1.83/0.98  fof(f7,axiom,(
% 1.83/0.98    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.83/0.98  
% 1.83/0.98  fof(f21,plain,(
% 1.83/0.98    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.83/0.98    inference(ennf_transformation,[],[f7])).
% 1.83/0.98  
% 1.83/0.98  fof(f57,plain,(
% 1.83/0.98    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.83/0.98    inference(cnf_transformation,[],[f21])).
% 1.83/0.98  
% 1.83/0.98  fof(f56,plain,(
% 1.83/0.98    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 1.83/0.98    inference(cnf_transformation,[],[f21])).
% 1.83/0.98  
% 1.83/0.98  fof(f80,plain,(
% 1.83/0.98    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.83/0.98    inference(equality_resolution,[],[f56])).
% 1.83/0.98  
% 1.83/0.98  fof(f8,axiom,(
% 1.83/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.83/0.98  
% 1.83/0.98  fof(f22,plain,(
% 1.83/0.98    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.83/0.98    inference(ennf_transformation,[],[f8])).
% 1.83/0.98  
% 1.83/0.98  fof(f23,plain,(
% 1.83/0.98    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.83/0.98    inference(flattening,[],[f22])).
% 1.83/0.98  
% 1.83/0.98  fof(f58,plain,(
% 1.83/0.98    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.83/0.98    inference(cnf_transformation,[],[f23])).
% 1.83/0.98  
% 1.83/0.98  cnf(c_3,plain,
% 1.83/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.83/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1912,plain,
% 1.83/0.98      ( ~ v1_xboole_0(k1_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(sK2) ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_705,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1530,plain,
% 1.83/0.98      ( k1_relset_1(k1_xboole_0,sK1,sK2) != X0
% 1.83/0.98      | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 1.83/0.98      | k1_xboole_0 != X0 ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_705]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1731,plain,
% 1.83/0.98      ( k1_relset_1(k1_xboole_0,sK1,sK2) != k1_relat_1(sK2)
% 1.83/0.98      | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 1.83/0.98      | k1_xboole_0 != k1_relat_1(sK2) ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_1530]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_19,plain,
% 1.83/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.83/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.83/0.98      inference(cnf_transformation,[],[f66]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1496,plain,
% 1.83/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 1.83/0.98      | k1_relset_1(X0,sK1,sK2) = k1_relat_1(sK2) ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_19]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1498,plain,
% 1.83/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 1.83/0.98      | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_relat_1(sK2) ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_1496]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_24,plain,
% 1.83/0.98      ( v1_funct_2(X0,X1,X2)
% 1.83/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.83/0.98      | k1_relset_1(X1,X2,X0) != X1
% 1.83/0.98      | k1_xboole_0 = X2 ),
% 1.83/0.98      inference(cnf_transformation,[],[f70]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_27,negated_conjecture,
% 1.83/0.98      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
% 1.83/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 1.83/0.98      | ~ v1_funct_1(sK2) ),
% 1.83/0.98      inference(cnf_transformation,[],[f77]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_29,negated_conjecture,
% 1.83/0.98      ( v1_funct_1(sK2) ),
% 1.83/0.98      inference(cnf_transformation,[],[f75]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_166,plain,
% 1.83/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 1.83/0.98      | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
% 1.83/0.98      inference(global_propositional_subsumption,
% 1.83/0.98                [status(thm)],
% 1.83/0.98                [c_27,c_29]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_167,negated_conjecture,
% 1.83/0.98      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
% 1.83/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
% 1.83/0.98      inference(renaming,[status(thm)],[c_166]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_513,plain,
% 1.83/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.83/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 1.83/0.98      | k1_relset_1(X1,X2,X0) != X1
% 1.83/0.98      | k1_relat_1(sK2) != X1
% 1.83/0.98      | sK1 != X2
% 1.83/0.98      | sK2 != X0
% 1.83/0.98      | k1_xboole_0 = X2 ),
% 1.83/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_167]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_514,plain,
% 1.83/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 1.83/0.98      | k1_relset_1(k1_relat_1(sK2),sK1,sK2) != k1_relat_1(sK2)
% 1.83/0.98      | k1_xboole_0 = sK1 ),
% 1.83/0.98      inference(unflattening,[status(thm)],[c_513]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_522,plain,
% 1.83/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 1.83/0.98      | k1_xboole_0 = sK1 ),
% 1.83/0.98      inference(forward_subsumption_resolution,
% 1.83/0.98                [status(thm)],
% 1.83/0.98                [c_514,c_19]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1141,plain,
% 1.83/0.98      ( k1_xboole_0 = sK1
% 1.83/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top ),
% 1.83/0.98      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_28,negated_conjecture,
% 1.83/0.98      ( r1_tarski(k2_relat_1(sK2),sK1) ),
% 1.83/0.98      inference(cnf_transformation,[],[f76]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_20,plain,
% 1.83/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.83/0.98      | ~ r1_tarski(k2_relat_1(X0),X2)
% 1.83/0.98      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.83/0.98      | ~ v1_relat_1(X0) ),
% 1.83/0.98      inference(cnf_transformation,[],[f67]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_30,negated_conjecture,
% 1.83/0.98      ( v1_relat_1(sK2) ),
% 1.83/0.98      inference(cnf_transformation,[],[f74]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_424,plain,
% 1.83/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.83/0.98      | ~ r1_tarski(k2_relat_1(X0),X2)
% 1.83/0.98      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.83/0.98      | sK2 != X0 ),
% 1.83/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_425,plain,
% 1.83/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.83/0.98      | ~ r1_tarski(k2_relat_1(sK2),X1)
% 1.83/0.98      | ~ r1_tarski(k1_relat_1(sK2),X0) ),
% 1.83/0.98      inference(unflattening,[status(thm)],[c_424]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1279,plain,
% 1.83/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 1.83/0.98      | ~ r1_tarski(k2_relat_1(sK2),sK1)
% 1.83/0.98      | ~ r1_tarski(k1_relat_1(sK2),X0) ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_425]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1365,plain,
% 1.83/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 1.83/0.98      | ~ r1_tarski(k2_relat_1(sK2),sK1)
% 1.83/0.98      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_1279]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_6,plain,
% 1.83/0.98      ( r1_tarski(X0,X0) ),
% 1.83/0.98      inference(cnf_transformation,[],[f79]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1366,plain,
% 1.83/0.98      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1415,plain,
% 1.83/0.98      ( k1_xboole_0 = sK1 ),
% 1.83/0.98      inference(global_propositional_subsumption,
% 1.83/0.98                [status(thm)],
% 1.83/0.98                [c_1141,c_28,c_522,c_1365,c_1366]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1148,plain,
% 1.83/0.98      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 1.83/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1420,plain,
% 1.83/0.98      ( r1_tarski(k2_relat_1(sK2),k1_xboole_0) = iProver_top ),
% 1.83/0.98      inference(demodulation,[status(thm)],[c_1415,c_1148]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_17,plain,
% 1.83/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0)) ),
% 1.83/0.98      inference(cnf_transformation,[],[f64]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1407,plain,
% 1.83/0.98      ( v1_xboole_0(k1_relat_1(sK2)) | ~ v1_xboole_0(sK2) ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1408,plain,
% 1.83/0.98      ( v1_xboole_0(k1_relat_1(sK2)) = iProver_top
% 1.83/0.98      | v1_xboole_0(sK2) != iProver_top ),
% 1.83/0.98      inference(predicate_to_equality,[status(thm)],[c_1407]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_707,plain,
% 1.83/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.83/0.98      theory(equality) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1402,plain,
% 1.83/0.98      ( ~ v1_xboole_0(X0)
% 1.83/0.98      | v1_xboole_0(k1_relat_1(sK2))
% 1.83/0.98      | k1_relat_1(sK2) != X0 ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_707]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1404,plain,
% 1.83/0.98      ( v1_xboole_0(k1_relat_1(sK2))
% 1.83/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 1.83/0.98      | k1_relat_1(sK2) != k1_xboole_0 ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_1402]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_708,plain,
% 1.83/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.83/0.98      theory(equality) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1371,plain,
% 1.83/0.98      ( ~ r1_tarski(X0,X1)
% 1.83/0.98      | r1_tarski(k1_relat_1(sK2),X2)
% 1.83/0.98      | X2 != X1
% 1.83/0.98      | k1_relat_1(sK2) != X0 ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_708]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1373,plain,
% 1.83/0.98      ( r1_tarski(k1_relat_1(sK2),k1_xboole_0)
% 1.83/0.98      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 1.83/0.98      | k1_relat_1(sK2) != k1_xboole_0
% 1.83/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_1371]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_12,plain,
% 1.83/0.98      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 1.83/0.98      inference(cnf_transformation,[],[f59]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1339,plain,
% 1.83/0.98      ( ~ v1_xboole_0(k1_relat_1(sK2))
% 1.83/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 1.83/0.98      | k1_relat_1(sK2) = k1_xboole_0 ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1340,plain,
% 1.83/0.98      ( k1_relat_1(sK2) = k1_xboole_0
% 1.83/0.98      | v1_xboole_0(k1_relat_1(sK2)) != iProver_top
% 1.83/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.83/0.98      inference(predicate_to_equality,[status(thm)],[c_1339]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1,plain,
% 1.83/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.83/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_15,plain,
% 1.83/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.83/0.98      | ~ r2_hidden(X2,X0)
% 1.83/0.98      | ~ v1_xboole_0(X1) ),
% 1.83/0.98      inference(cnf_transformation,[],[f62]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_13,plain,
% 1.83/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.83/0.98      inference(cnf_transformation,[],[f61]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_235,plain,
% 1.83/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.83/0.98      inference(prop_impl,[status(thm)],[c_13]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_236,plain,
% 1.83/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.83/0.98      inference(renaming,[status(thm)],[c_235]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_289,plain,
% 1.83/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 1.83/0.98      inference(bin_hyper_res,[status(thm)],[c_15,c_236]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_405,plain,
% 1.83/0.98      ( ~ r1_tarski(X0,X1)
% 1.83/0.98      | ~ v1_xboole_0(X1)
% 1.83/0.98      | v1_xboole_0(X2)
% 1.83/0.98      | X0 != X2
% 1.83/0.98      | sK0(X2) != X3 ),
% 1.83/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_289]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_406,plain,
% 1.83/0.98      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 1.83/0.98      inference(unflattening,[status(thm)],[c_405]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1303,plain,
% 1.83/0.98      ( ~ r1_tarski(k2_relat_1(sK2),X0)
% 1.83/0.98      | ~ v1_xboole_0(X0)
% 1.83/0.98      | v1_xboole_0(k2_relat_1(sK2)) ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_406]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1304,plain,
% 1.83/0.98      ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 1.83/0.98      | v1_xboole_0(X0) != iProver_top
% 1.83/0.98      | v1_xboole_0(k2_relat_1(sK2)) = iProver_top ),
% 1.83/0.98      inference(predicate_to_equality,[status(thm)],[c_1303]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1306,plain,
% 1.83/0.98      ( r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top
% 1.83/0.98      | v1_xboole_0(k2_relat_1(sK2)) = iProver_top
% 1.83/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_1304]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_1281,plain,
% 1.83/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 1.83/0.98      | ~ r1_tarski(k2_relat_1(sK2),sK1)
% 1.83/0.98      | ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0) ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_1279]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_23,plain,
% 1.83/0.98      ( v1_funct_2(X0,k1_xboole_0,X1)
% 1.83/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.83/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 1.83/0.98      inference(cnf_transformation,[],[f84]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_497,plain,
% 1.83/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.83/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 1.83/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 1.83/0.98      | k1_relat_1(sK2) != k1_xboole_0
% 1.83/0.98      | sK1 != X1
% 1.83/0.98      | sK2 != X0 ),
% 1.83/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_167]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_498,plain,
% 1.83/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 1.83/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 1.83/0.98      | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
% 1.83/0.98      | k1_relat_1(sK2) != k1_xboole_0 ),
% 1.83/0.98      inference(unflattening,[status(thm)],[c_497]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_18,plain,
% 1.83/0.98      ( ~ v1_relat_1(X0)
% 1.83/0.98      | v1_xboole_0(X0)
% 1.83/0.98      | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 1.83/0.98      inference(cnf_transformation,[],[f65]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_439,plain,
% 1.83/0.98      ( v1_xboole_0(X0) | ~ v1_xboole_0(k2_relat_1(X0)) | sK2 != X0 ),
% 1.83/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_440,plain,
% 1.83/0.98      ( ~ v1_xboole_0(k2_relat_1(sK2)) | v1_xboole_0(sK2) ),
% 1.83/0.98      inference(unflattening,[status(thm)],[c_439]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_441,plain,
% 1.83/0.98      ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top
% 1.83/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 1.83/0.98      inference(predicate_to_equality,[status(thm)],[c_440]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_8,plain,
% 1.83/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 1.83/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_87,plain,
% 1.83/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.83/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_89,plain,
% 1.83/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_87]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_88,plain,
% 1.83/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_9,plain,
% 1.83/0.98      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 1.83/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_85,plain,
% 1.83/0.98      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 1.83/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_10,plain,
% 1.83/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 1.83/0.98      inference(cnf_transformation,[],[f80]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_83,plain,
% 1.83/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 1.83/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_11,plain,
% 1.83/0.98      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 1.83/0.98      inference(cnf_transformation,[],[f58]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_80,plain,
% 1.83/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 1.83/0.98      | r1_tarski(X0,X1) != iProver_top
% 1.83/0.98      | v1_xboole_0(X0) = iProver_top ),
% 1.83/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_82,plain,
% 1.83/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 1.83/0.98      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 1.83/0.98      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_80]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(c_81,plain,
% 1.83/0.98      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 1.83/0.98      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 1.83/0.98      | v1_xboole_0(k1_xboole_0) ),
% 1.83/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 1.83/0.98  
% 1.83/0.98  cnf(contradiction,plain,
% 1.83/0.98      ( $false ),
% 1.83/0.98      inference(minisat,
% 1.83/0.98                [status(thm)],
% 1.83/0.98                [c_1912,c_1731,c_1498,c_1420,c_1408,c_1404,c_1373,c_1366,
% 1.83/0.98                 c_1365,c_1340,c_1306,c_1281,c_498,c_441,c_89,c_88,c_85,
% 1.83/0.98                 c_83,c_10,c_82,c_81,c_28]) ).
% 1.83/0.98  
% 1.83/0.98  
% 1.83/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.83/0.98  
% 1.83/0.98  ------                               Statistics
% 1.83/0.98  
% 1.83/0.98  ------ General
% 1.83/0.98  
% 1.83/0.98  abstr_ref_over_cycles:                  0
% 1.83/0.98  abstr_ref_under_cycles:                 0
% 1.83/0.98  gc_basic_clause_elim:                   0
% 1.83/0.98  forced_gc_time:                         0
% 1.83/0.98  parsing_time:                           0.009
% 1.83/0.98  unif_index_cands_time:                  0.
% 1.83/0.98  unif_index_add_time:                    0.
% 1.83/0.98  orderings_time:                         0.
% 1.83/0.98  out_proof_time:                         0.011
% 1.83/0.98  total_time:                             0.084
% 1.83/0.98  num_of_symbols:                         50
% 1.83/0.98  num_of_terms:                           1320
% 1.83/0.98  
% 1.83/0.98  ------ Preprocessing
% 1.83/0.98  
% 1.83/0.98  num_of_splits:                          0
% 1.83/0.98  num_of_split_atoms:                     0
% 1.83/0.98  num_of_reused_defs:                     0
% 1.83/0.98  num_eq_ax_congr_red:                    5
% 1.83/0.98  num_of_sem_filtered_clauses:            2
% 1.83/0.98  num_of_subtypes:                        0
% 1.83/0.98  monotx_restored_types:                  0
% 1.83/0.98  sat_num_of_epr_types:                   0
% 1.83/0.98  sat_num_of_non_cyclic_types:            0
% 1.83/0.98  sat_guarded_non_collapsed_types:        0
% 1.83/0.98  num_pure_diseq_elim:                    0
% 1.83/0.98  simp_replaced_by:                       0
% 1.83/0.98  res_preprocessed:                       115
% 1.83/0.98  prep_upred:                             0
% 1.83/0.98  prep_unflattend:                        36
% 1.83/0.98  smt_new_axioms:                         0
% 1.83/0.98  pred_elim_cands:                        3
% 1.83/0.98  pred_elim:                              4
% 1.83/0.98  pred_elim_cl:                           9
% 1.83/0.98  pred_elim_cycles:                       6
% 1.83/0.98  merged_defs:                            8
% 1.83/0.98  merged_defs_ncl:                        0
% 1.83/0.98  bin_hyper_res:                          9
% 1.83/0.98  prep_cycles:                            4
% 1.83/0.98  pred_elim_time:                         0.004
% 1.83/0.98  splitting_time:                         0.
% 1.83/0.98  sem_filter_time:                        0.
% 1.83/0.98  monotx_time:                            0.
% 1.83/0.98  subtype_inf_time:                       0.
% 1.83/0.98  
% 1.83/0.98  ------ Problem properties
% 1.83/0.98  
% 1.83/0.98  clauses:                                20
% 1.83/0.98  conjectures:                            1
% 1.83/0.98  epr:                                    7
% 1.83/0.98  horn:                                   20
% 1.83/0.98  ground:                                 7
% 1.83/0.98  unary:                                  7
% 1.83/0.98  binary:                                 7
% 1.83/0.98  lits:                                   42
% 1.83/0.98  lits_eq:                                13
% 1.83/0.98  fd_pure:                                0
% 1.83/0.98  fd_pseudo:                              0
% 1.83/0.98  fd_cond:                                1
% 1.83/0.98  fd_pseudo_cond:                         2
% 1.83/0.98  ac_symbols:                             0
% 1.83/0.98  
% 1.83/0.98  ------ Propositional Solver
% 1.83/0.98  
% 1.83/0.98  prop_solver_calls:                      26
% 1.83/0.98  prop_fast_solver_calls:                 599
% 1.83/0.98  smt_solver_calls:                       0
% 1.83/0.98  smt_fast_solver_calls:                  0
% 1.83/0.98  prop_num_of_clauses:                    487
% 1.83/0.98  prop_preprocess_simplified:             3288
% 1.83/0.98  prop_fo_subsumed:                       9
% 1.83/0.98  prop_solver_time:                       0.
% 1.83/0.98  smt_solver_time:                        0.
% 1.83/0.98  smt_fast_solver_time:                   0.
% 1.83/0.98  prop_fast_solver_time:                  0.
% 1.83/0.98  prop_unsat_core_time:                   0.
% 1.83/0.98  
% 1.83/0.98  ------ QBF
% 1.83/0.98  
% 1.83/0.98  qbf_q_res:                              0
% 1.83/0.98  qbf_num_tautologies:                    0
% 1.83/0.98  qbf_prep_cycles:                        0
% 1.83/0.98  
% 1.83/0.98  ------ BMC1
% 1.83/0.98  
% 1.83/0.98  bmc1_current_bound:                     -1
% 1.83/0.98  bmc1_last_solved_bound:                 -1
% 1.83/0.98  bmc1_unsat_core_size:                   -1
% 1.83/0.98  bmc1_unsat_core_parents_size:           -1
% 1.83/0.98  bmc1_merge_next_fun:                    0
% 1.83/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.83/0.98  
% 1.83/0.98  ------ Instantiation
% 1.83/0.98  
% 1.83/0.98  inst_num_of_clauses:                    140
% 1.83/0.98  inst_num_in_passive:                    41
% 1.83/0.98  inst_num_in_active:                     93
% 1.83/0.98  inst_num_in_unprocessed:                5
% 1.83/0.98  inst_num_of_loops:                      118
% 1.83/0.98  inst_num_of_learning_restarts:          0
% 1.83/0.98  inst_num_moves_active_passive:          22
% 1.83/0.98  inst_lit_activity:                      0
% 1.83/0.98  inst_lit_activity_moves:                0
% 1.83/0.98  inst_num_tautologies:                   0
% 1.83/0.98  inst_num_prop_implied:                  0
% 1.83/0.98  inst_num_existing_simplified:           0
% 1.83/0.98  inst_num_eq_res_simplified:             0
% 1.83/0.98  inst_num_child_elim:                    0
% 1.83/0.98  inst_num_of_dismatching_blockings:      14
% 1.83/0.98  inst_num_of_non_proper_insts:           105
% 1.83/0.98  inst_num_of_duplicates:                 0
% 1.83/0.98  inst_inst_num_from_inst_to_res:         0
% 1.83/0.98  inst_dismatching_checking_time:         0.
% 1.83/0.98  
% 1.83/0.98  ------ Resolution
% 1.83/0.98  
% 1.83/0.98  res_num_of_clauses:                     0
% 1.83/0.98  res_num_in_passive:                     0
% 1.83/0.98  res_num_in_active:                      0
% 1.83/0.98  res_num_of_loops:                       119
% 1.83/0.98  res_forward_subset_subsumed:            0
% 1.83/0.98  res_backward_subset_subsumed:           0
% 1.83/0.98  res_forward_subsumed:                   0
% 1.83/0.98  res_backward_subsumed:                  0
% 1.83/0.98  res_forward_subsumption_resolution:     1
% 1.83/0.98  res_backward_subsumption_resolution:    0
% 1.83/0.98  res_clause_to_clause_subsumption:       83
% 1.83/0.98  res_orphan_elimination:                 0
% 1.83/0.98  res_tautology_del:                      32
% 1.83/0.98  res_num_eq_res_simplified:              0
% 1.83/0.98  res_num_sel_changes:                    0
% 1.83/0.98  res_moves_from_active_to_pass:          0
% 1.83/0.98  
% 1.83/0.98  ------ Superposition
% 1.83/0.98  
% 1.83/0.98  sup_time_total:                         0.
% 1.83/0.98  sup_time_generating:                    0.
% 1.83/0.98  sup_time_sim_full:                      0.
% 1.83/0.98  sup_time_sim_immed:                     0.
% 1.83/0.98  
% 1.83/0.98  sup_num_of_clauses:                     24
% 1.83/0.98  sup_num_in_active:                      11
% 1.83/0.98  sup_num_in_passive:                     13
% 1.83/0.98  sup_num_of_loops:                       22
% 1.83/0.98  sup_fw_superposition:                   8
% 1.83/0.98  sup_bw_superposition:                   8
% 1.83/0.98  sup_immediate_simplified:               4
% 1.83/0.98  sup_given_eliminated:                   0
% 1.83/0.98  comparisons_done:                       0
% 1.83/0.98  comparisons_avoided:                    0
% 1.83/0.98  
% 1.83/0.98  ------ Simplifications
% 1.83/0.98  
% 1.83/0.98  
% 1.83/0.98  sim_fw_subset_subsumed:                 2
% 1.83/0.98  sim_bw_subset_subsumed:                 0
% 1.83/0.98  sim_fw_subsumed:                        0
% 1.83/0.98  sim_bw_subsumed:                        1
% 1.83/0.98  sim_fw_subsumption_res:                 0
% 1.83/0.98  sim_bw_subsumption_res:                 0
% 1.83/0.98  sim_tautology_del:                      0
% 1.83/0.98  sim_eq_tautology_del:                   1
% 1.83/0.98  sim_eq_res_simp:                        1
% 1.83/0.98  sim_fw_demodulated:                     0
% 1.83/0.98  sim_bw_demodulated:                     11
% 1.83/0.98  sim_light_normalised:                   1
% 1.83/0.98  sim_joinable_taut:                      0
% 1.83/0.98  sim_joinable_simp:                      0
% 1.83/0.98  sim_ac_normalised:                      0
% 1.83/0.98  sim_smt_subsumption:                    0
% 1.83/0.98  
%------------------------------------------------------------------------------
