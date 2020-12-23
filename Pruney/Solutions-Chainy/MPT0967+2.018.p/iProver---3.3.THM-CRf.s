%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:40 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 287 expanded)
%              Number of clauses        :   92 ( 131 expanded)
%              Number of leaves         :   15 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  469 (1368 expanded)
%              Number of equality atoms :  211 ( 461 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f37])).

fof(f63,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2661,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_5319,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2661])).

cnf(c_750,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2909,plain,
    ( k1_relset_1(sK0,sK2,sK3) != X0
    | k1_relset_1(sK0,sK2,sK3) = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_5176,plain,
    ( k1_relset_1(sK0,sK2,sK3) != k1_relat_1(sK3)
    | k1_relset_1(sK0,sK2,sK3) = sK0
    | sK0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2909])).

cnf(c_3093,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_5020,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3093])).

cnf(c_5021,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_5020])).

cnf(c_1429,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_2671,plain,
    ( k1_relat_1(sK3) != X0
    | sK0 != X0
    | sK0 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1429])).

cnf(c_3405,plain,
    ( k1_relat_1(sK3) != sK0
    | sK0 = k1_relat_1(sK3)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2671])).

cnf(c_749,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3090,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_501,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_503,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_501,c_26])).

cnf(c_1190,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1193,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2691,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1190,c_1193])).

cnf(c_2731,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_503,c_2691])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_88,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_89,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_14,c_9])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_350,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_12])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_350])).

cnf(c_1375,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_1384,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_1427,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1384])).

cnf(c_1428,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_1828,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_751,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1526,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK3),X2)
    | X2 != X1
    | k1_relat_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_1827,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0)
    | r1_tarski(k1_relat_1(sK3),X1)
    | X1 != X0
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1526])).

cnf(c_2175,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | X0 != sK0
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1827])).

cnf(c_2177,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2175])).

cnf(c_1831,plain,
    ( X0 != X1
    | k1_relat_1(sK3) != X1
    | k1_relat_1(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_2183,plain,
    ( X0 != k1_relat_1(sK3)
    | k1_relat_1(sK3) = X0
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1831])).

cnf(c_2184,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2183])).

cnf(c_2227,plain,
    ( X0 != X1
    | X0 = sK1
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_2228,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2227])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2656,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2670,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = sK0
    | sK0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2183])).

cnf(c_2672,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | sK0 = k1_relat_1(sK3)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2671])).

cnf(c_2877,plain,
    ( k1_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2731,c_26,c_24,c_88,c_89,c_1375,c_1427,c_1428,c_1828,c_2177,c_2184,c_2228,c_2656,c_2670,c_2672])).

cnf(c_1732,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,X2)
    | X2 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_1968,plain,
    ( ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,X1)
    | X1 != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1732])).

cnf(c_2597,plain,
    ( r1_tarski(sK1,X0)
    | ~ r1_tarski(sK1,sK2)
    | X0 != sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1968])).

cnf(c_2599,plain,
    ( ~ r1_tarski(sK1,sK2)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != sK1
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2597])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1409,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k2_relat_1(sK3),X1)
    | ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1871,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1409])).

cnf(c_2353,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1871])).

cnf(c_2222,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1475,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | r1_tarski(k2_relat_1(sK3),X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1626,plain,
    ( r1_tarski(k2_relat_1(sK3),X0)
    | ~ r1_tarski(k2_relat_1(sK3),sK1)
    | ~ r1_tarski(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_1475])).

cnf(c_1729,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1626])).

cnf(c_1432,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_1642,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_1643,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_1608,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_1431,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_1385,plain,
    ( sK1 != X0
    | sK1 = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_1386,plain,
    ( sK1 = sK2
    | sK1 != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_11])).

cnf(c_371,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_12])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_371])).

cnf(c_1381,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_1365,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_23,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_149,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_28])).

cnf(c_150,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(renaming,[status(thm)],[c_149])).

cnf(c_511,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | sK1 != sK2
    | sK0 != sK0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_150,c_27])).

cnf(c_20,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_487,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_150])).

cnf(c_488,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5319,c_5176,c_5021,c_3405,c_3090,c_2877,c_2599,c_2353,c_2222,c_1729,c_1643,c_1608,c_1431,c_1428,c_1386,c_1381,c_1375,c_1365,c_511,c_488,c_25,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : iproveropt_run.sh %d %s
% 0.06/0.25  % Computer   : n017.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 19:44:46 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  % Running in FOF mode
% 2.73/0.89  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/0.89  
% 2.73/0.89  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.73/0.89  
% 2.73/0.89  ------  iProver source info
% 2.73/0.89  
% 2.73/0.89  git: date: 2020-06-30 10:37:57 +0100
% 2.73/0.89  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.73/0.89  git: non_committed_changes: false
% 2.73/0.89  git: last_make_outside_of_git: false
% 2.73/0.89  
% 2.73/0.89  ------ 
% 2.73/0.89  
% 2.73/0.89  ------ Input Options
% 2.73/0.89  
% 2.73/0.89  --out_options                           all
% 2.73/0.89  --tptp_safe_out                         true
% 2.73/0.89  --problem_path                          ""
% 2.73/0.89  --include_path                          ""
% 2.73/0.89  --clausifier                            res/vclausify_rel
% 2.73/0.89  --clausifier_options                    --mode clausify
% 2.73/0.89  --stdin                                 false
% 2.73/0.89  --stats_out                             all
% 2.73/0.89  
% 2.73/0.89  ------ General Options
% 2.73/0.89  
% 2.73/0.89  --fof                                   false
% 2.73/0.89  --time_out_real                         305.
% 2.73/0.89  --time_out_virtual                      -1.
% 2.73/0.89  --symbol_type_check                     false
% 2.73/0.89  --clausify_out                          false
% 2.73/0.89  --sig_cnt_out                           false
% 2.73/0.89  --trig_cnt_out                          false
% 2.73/0.89  --trig_cnt_out_tolerance                1.
% 2.73/0.89  --trig_cnt_out_sk_spl                   false
% 2.73/0.89  --abstr_cl_out                          false
% 2.73/0.89  
% 2.73/0.89  ------ Global Options
% 2.73/0.89  
% 2.73/0.89  --schedule                              default
% 2.73/0.89  --add_important_lit                     false
% 2.73/0.89  --prop_solver_per_cl                    1000
% 2.73/0.89  --min_unsat_core                        false
% 2.73/0.89  --soft_assumptions                      false
% 2.73/0.89  --soft_lemma_size                       3
% 2.73/0.89  --prop_impl_unit_size                   0
% 2.73/0.89  --prop_impl_unit                        []
% 2.73/0.89  --share_sel_clauses                     true
% 2.73/0.89  --reset_solvers                         false
% 2.73/0.89  --bc_imp_inh                            [conj_cone]
% 2.73/0.89  --conj_cone_tolerance                   3.
% 2.73/0.89  --extra_neg_conj                        none
% 2.73/0.89  --large_theory_mode                     true
% 2.73/0.89  --prolific_symb_bound                   200
% 2.73/0.89  --lt_threshold                          2000
% 2.73/0.89  --clause_weak_htbl                      true
% 2.73/0.89  --gc_record_bc_elim                     false
% 2.73/0.89  
% 2.73/0.89  ------ Preprocessing Options
% 2.73/0.89  
% 2.73/0.89  --preprocessing_flag                    true
% 2.73/0.89  --time_out_prep_mult                    0.1
% 2.73/0.89  --splitting_mode                        input
% 2.73/0.89  --splitting_grd                         true
% 2.73/0.89  --splitting_cvd                         false
% 2.73/0.89  --splitting_cvd_svl                     false
% 2.73/0.89  --splitting_nvd                         32
% 2.73/0.89  --sub_typing                            true
% 2.73/0.89  --prep_gs_sim                           true
% 2.73/0.89  --prep_unflatten                        true
% 2.73/0.89  --prep_res_sim                          true
% 2.73/0.89  --prep_upred                            true
% 2.73/0.89  --prep_sem_filter                       exhaustive
% 2.73/0.89  --prep_sem_filter_out                   false
% 2.73/0.89  --pred_elim                             true
% 2.73/0.89  --res_sim_input                         true
% 2.73/0.89  --eq_ax_congr_red                       true
% 2.73/0.89  --pure_diseq_elim                       true
% 2.73/0.89  --brand_transform                       false
% 2.73/0.89  --non_eq_to_eq                          false
% 2.73/0.89  --prep_def_merge                        true
% 2.73/0.89  --prep_def_merge_prop_impl              false
% 2.73/0.89  --prep_def_merge_mbd                    true
% 2.73/0.89  --prep_def_merge_tr_red                 false
% 2.73/0.89  --prep_def_merge_tr_cl                  false
% 2.73/0.89  --smt_preprocessing                     true
% 2.73/0.89  --smt_ac_axioms                         fast
% 2.73/0.89  --preprocessed_out                      false
% 2.73/0.89  --preprocessed_stats                    false
% 2.73/0.89  
% 2.73/0.89  ------ Abstraction refinement Options
% 2.73/0.89  
% 2.73/0.89  --abstr_ref                             []
% 2.73/0.89  --abstr_ref_prep                        false
% 2.73/0.89  --abstr_ref_until_sat                   false
% 2.73/0.89  --abstr_ref_sig_restrict                funpre
% 2.73/0.89  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/0.89  --abstr_ref_under                       []
% 2.73/0.89  
% 2.73/0.89  ------ SAT Options
% 2.73/0.89  
% 2.73/0.89  --sat_mode                              false
% 2.73/0.89  --sat_fm_restart_options                ""
% 2.73/0.89  --sat_gr_def                            false
% 2.73/0.89  --sat_epr_types                         true
% 2.73/0.89  --sat_non_cyclic_types                  false
% 2.73/0.89  --sat_finite_models                     false
% 2.73/0.89  --sat_fm_lemmas                         false
% 2.73/0.89  --sat_fm_prep                           false
% 2.73/0.89  --sat_fm_uc_incr                        true
% 2.73/0.89  --sat_out_model                         small
% 2.73/0.89  --sat_out_clauses                       false
% 2.73/0.89  
% 2.73/0.89  ------ QBF Options
% 2.73/0.89  
% 2.73/0.89  --qbf_mode                              false
% 2.73/0.89  --qbf_elim_univ                         false
% 2.73/0.89  --qbf_dom_inst                          none
% 2.73/0.89  --qbf_dom_pre_inst                      false
% 2.73/0.89  --qbf_sk_in                             false
% 2.73/0.89  --qbf_pred_elim                         true
% 2.73/0.89  --qbf_split                             512
% 2.73/0.89  
% 2.73/0.89  ------ BMC1 Options
% 2.73/0.89  
% 2.73/0.89  --bmc1_incremental                      false
% 2.73/0.89  --bmc1_axioms                           reachable_all
% 2.73/0.89  --bmc1_min_bound                        0
% 2.73/0.89  --bmc1_max_bound                        -1
% 2.73/0.89  --bmc1_max_bound_default                -1
% 2.73/0.89  --bmc1_symbol_reachability              true
% 2.73/0.89  --bmc1_property_lemmas                  false
% 2.73/0.89  --bmc1_k_induction                      false
% 2.73/0.89  --bmc1_non_equiv_states                 false
% 2.73/0.89  --bmc1_deadlock                         false
% 2.73/0.89  --bmc1_ucm                              false
% 2.73/0.89  --bmc1_add_unsat_core                   none
% 2.73/0.89  --bmc1_unsat_core_children              false
% 2.73/0.89  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/0.89  --bmc1_out_stat                         full
% 2.73/0.89  --bmc1_ground_init                      false
% 2.73/0.89  --bmc1_pre_inst_next_state              false
% 2.73/0.89  --bmc1_pre_inst_state                   false
% 2.73/0.89  --bmc1_pre_inst_reach_state             false
% 2.73/0.89  --bmc1_out_unsat_core                   false
% 2.73/0.89  --bmc1_aig_witness_out                  false
% 2.73/0.89  --bmc1_verbose                          false
% 2.73/0.89  --bmc1_dump_clauses_tptp                false
% 2.73/0.89  --bmc1_dump_unsat_core_tptp             false
% 2.73/0.89  --bmc1_dump_file                        -
% 2.73/0.89  --bmc1_ucm_expand_uc_limit              128
% 2.73/0.89  --bmc1_ucm_n_expand_iterations          6
% 2.73/0.89  --bmc1_ucm_extend_mode                  1
% 2.73/0.89  --bmc1_ucm_init_mode                    2
% 2.73/0.89  --bmc1_ucm_cone_mode                    none
% 2.73/0.89  --bmc1_ucm_reduced_relation_type        0
% 2.73/0.89  --bmc1_ucm_relax_model                  4
% 2.73/0.89  --bmc1_ucm_full_tr_after_sat            true
% 2.73/0.89  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/0.89  --bmc1_ucm_layered_model                none
% 2.73/0.89  --bmc1_ucm_max_lemma_size               10
% 2.73/0.89  
% 2.73/0.89  ------ AIG Options
% 2.73/0.89  
% 2.73/0.89  --aig_mode                              false
% 2.73/0.89  
% 2.73/0.89  ------ Instantiation Options
% 2.73/0.89  
% 2.73/0.89  --instantiation_flag                    true
% 2.73/0.89  --inst_sos_flag                         false
% 2.73/0.89  --inst_sos_phase                        true
% 2.73/0.89  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/0.89  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/0.89  --inst_lit_sel_side                     num_symb
% 2.73/0.89  --inst_solver_per_active                1400
% 2.73/0.89  --inst_solver_calls_frac                1.
% 2.73/0.89  --inst_passive_queue_type               priority_queues
% 2.73/0.89  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/0.89  --inst_passive_queues_freq              [25;2]
% 2.73/0.89  --inst_dismatching                      true
% 2.73/0.89  --inst_eager_unprocessed_to_passive     true
% 2.73/0.89  --inst_prop_sim_given                   true
% 2.73/0.89  --inst_prop_sim_new                     false
% 2.73/0.89  --inst_subs_new                         false
% 2.73/0.89  --inst_eq_res_simp                      false
% 2.73/0.89  --inst_subs_given                       false
% 2.73/0.89  --inst_orphan_elimination               true
% 2.73/0.89  --inst_learning_loop_flag               true
% 2.73/0.89  --inst_learning_start                   3000
% 2.73/0.89  --inst_learning_factor                  2
% 2.73/0.89  --inst_start_prop_sim_after_learn       3
% 2.73/0.89  --inst_sel_renew                        solver
% 2.73/0.89  --inst_lit_activity_flag                true
% 2.73/0.89  --inst_restr_to_given                   false
% 2.73/0.89  --inst_activity_threshold               500
% 2.73/0.89  --inst_out_proof                        true
% 2.73/0.89  
% 2.73/0.89  ------ Resolution Options
% 2.73/0.89  
% 2.73/0.89  --resolution_flag                       true
% 2.73/0.89  --res_lit_sel                           adaptive
% 2.73/0.89  --res_lit_sel_side                      none
% 2.73/0.89  --res_ordering                          kbo
% 2.73/0.89  --res_to_prop_solver                    active
% 2.73/0.89  --res_prop_simpl_new                    false
% 2.73/0.89  --res_prop_simpl_given                  true
% 2.73/0.89  --res_passive_queue_type                priority_queues
% 2.73/0.89  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/0.89  --res_passive_queues_freq               [15;5]
% 2.73/0.89  --res_forward_subs                      full
% 2.73/0.89  --res_backward_subs                     full
% 2.73/0.89  --res_forward_subs_resolution           true
% 2.73/0.89  --res_backward_subs_resolution          true
% 2.73/0.89  --res_orphan_elimination                true
% 2.73/0.89  --res_time_limit                        2.
% 2.73/0.89  --res_out_proof                         true
% 2.73/0.89  
% 2.73/0.89  ------ Superposition Options
% 2.73/0.89  
% 2.73/0.89  --superposition_flag                    true
% 2.73/0.89  --sup_passive_queue_type                priority_queues
% 2.73/0.89  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/0.89  --sup_passive_queues_freq               [8;1;4]
% 2.73/0.89  --demod_completeness_check              fast
% 2.73/0.89  --demod_use_ground                      true
% 2.73/0.89  --sup_to_prop_solver                    passive
% 2.73/0.89  --sup_prop_simpl_new                    true
% 2.73/0.89  --sup_prop_simpl_given                  true
% 2.73/0.89  --sup_fun_splitting                     false
% 2.73/0.89  --sup_smt_interval                      50000
% 2.73/0.89  
% 2.73/0.89  ------ Superposition Simplification Setup
% 2.73/0.89  
% 2.73/0.89  --sup_indices_passive                   []
% 2.73/0.89  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.89  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.89  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.89  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/0.89  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.89  --sup_full_bw                           [BwDemod]
% 2.73/0.89  --sup_immed_triv                        [TrivRules]
% 2.73/0.89  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/0.89  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.89  --sup_immed_bw_main                     []
% 2.73/0.89  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.89  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/0.89  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.89  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.89  
% 2.73/0.89  ------ Combination Options
% 2.73/0.89  
% 2.73/0.89  --comb_res_mult                         3
% 2.73/0.89  --comb_sup_mult                         2
% 2.73/0.89  --comb_inst_mult                        10
% 2.73/0.89  
% 2.73/0.89  ------ Debug Options
% 2.73/0.89  
% 2.73/0.89  --dbg_backtrace                         false
% 2.73/0.89  --dbg_dump_prop_clauses                 false
% 2.73/0.89  --dbg_dump_prop_clauses_file            -
% 2.73/0.89  --dbg_out_stat                          false
% 2.73/0.89  ------ Parsing...
% 2.73/0.89  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.73/0.89  
% 2.73/0.89  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.73/0.89  
% 2.73/0.89  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.73/0.89  
% 2.73/0.89  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.73/0.89  ------ Proving...
% 2.73/0.89  ------ Problem Properties 
% 2.73/0.89  
% 2.73/0.89  
% 2.73/0.89  clauses                                 23
% 2.73/0.89  conjectures                             3
% 2.73/0.89  EPR                                     4
% 2.73/0.89  Horn                                    20
% 2.73/0.89  unary                                   5
% 2.73/0.89  binary                                  10
% 2.73/0.89  lits                                    53
% 2.73/0.89  lits eq                                 24
% 2.73/0.89  fd_pure                                 0
% 2.73/0.89  fd_pseudo                               0
% 2.73/0.89  fd_cond                                 2
% 2.73/0.89  fd_pseudo_cond                          0
% 2.73/0.89  AC symbols                              0
% 2.73/0.89  
% 2.73/0.89  ------ Schedule dynamic 5 is on 
% 2.73/0.89  
% 2.73/0.89  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.73/0.89  
% 2.73/0.89  
% 2.73/0.89  ------ 
% 2.73/0.89  Current options:
% 2.73/0.89  ------ 
% 2.73/0.89  
% 2.73/0.89  ------ Input Options
% 2.73/0.89  
% 2.73/0.89  --out_options                           all
% 2.73/0.89  --tptp_safe_out                         true
% 2.73/0.89  --problem_path                          ""
% 2.73/0.89  --include_path                          ""
% 2.73/0.89  --clausifier                            res/vclausify_rel
% 2.73/0.89  --clausifier_options                    --mode clausify
% 2.73/0.89  --stdin                                 false
% 2.73/0.89  --stats_out                             all
% 2.73/0.89  
% 2.73/0.89  ------ General Options
% 2.73/0.89  
% 2.73/0.89  --fof                                   false
% 2.73/0.89  --time_out_real                         305.
% 2.73/0.89  --time_out_virtual                      -1.
% 2.73/0.89  --symbol_type_check                     false
% 2.73/0.89  --clausify_out                          false
% 2.73/0.89  --sig_cnt_out                           false
% 2.73/0.89  --trig_cnt_out                          false
% 2.73/0.89  --trig_cnt_out_tolerance                1.
% 2.73/0.89  --trig_cnt_out_sk_spl                   false
% 2.73/0.89  --abstr_cl_out                          false
% 2.73/0.89  
% 2.73/0.89  ------ Global Options
% 2.73/0.89  
% 2.73/0.89  --schedule                              default
% 2.73/0.89  --add_important_lit                     false
% 2.73/0.89  --prop_solver_per_cl                    1000
% 2.73/0.89  --min_unsat_core                        false
% 2.73/0.89  --soft_assumptions                      false
% 2.73/0.89  --soft_lemma_size                       3
% 2.73/0.89  --prop_impl_unit_size                   0
% 2.73/0.89  --prop_impl_unit                        []
% 2.73/0.89  --share_sel_clauses                     true
% 2.73/0.89  --reset_solvers                         false
% 2.73/0.89  --bc_imp_inh                            [conj_cone]
% 2.73/0.89  --conj_cone_tolerance                   3.
% 2.73/0.89  --extra_neg_conj                        none
% 2.73/0.89  --large_theory_mode                     true
% 2.73/0.89  --prolific_symb_bound                   200
% 2.73/0.89  --lt_threshold                          2000
% 2.73/0.89  --clause_weak_htbl                      true
% 2.73/0.89  --gc_record_bc_elim                     false
% 2.73/0.89  
% 2.73/0.89  ------ Preprocessing Options
% 2.73/0.89  
% 2.73/0.89  --preprocessing_flag                    true
% 2.73/0.89  --time_out_prep_mult                    0.1
% 2.73/0.89  --splitting_mode                        input
% 2.73/0.89  --splitting_grd                         true
% 2.73/0.89  --splitting_cvd                         false
% 2.73/0.89  --splitting_cvd_svl                     false
% 2.73/0.89  --splitting_nvd                         32
% 2.73/0.89  --sub_typing                            true
% 2.73/0.89  --prep_gs_sim                           true
% 2.73/0.89  --prep_unflatten                        true
% 2.73/0.89  --prep_res_sim                          true
% 2.73/0.89  --prep_upred                            true
% 2.73/0.89  --prep_sem_filter                       exhaustive
% 2.73/0.89  --prep_sem_filter_out                   false
% 2.73/0.89  --pred_elim                             true
% 2.73/0.89  --res_sim_input                         true
% 2.73/0.89  --eq_ax_congr_red                       true
% 2.73/0.89  --pure_diseq_elim                       true
% 2.73/0.89  --brand_transform                       false
% 2.73/0.89  --non_eq_to_eq                          false
% 2.73/0.89  --prep_def_merge                        true
% 2.73/0.89  --prep_def_merge_prop_impl              false
% 2.73/0.89  --prep_def_merge_mbd                    true
% 2.73/0.89  --prep_def_merge_tr_red                 false
% 2.73/0.89  --prep_def_merge_tr_cl                  false
% 2.73/0.89  --smt_preprocessing                     true
% 2.73/0.89  --smt_ac_axioms                         fast
% 2.73/0.89  --preprocessed_out                      false
% 2.73/0.89  --preprocessed_stats                    false
% 2.73/0.89  
% 2.73/0.89  ------ Abstraction refinement Options
% 2.73/0.89  
% 2.73/0.89  --abstr_ref                             []
% 2.73/0.89  --abstr_ref_prep                        false
% 2.73/0.89  --abstr_ref_until_sat                   false
% 2.73/0.89  --abstr_ref_sig_restrict                funpre
% 2.73/0.89  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/0.89  --abstr_ref_under                       []
% 2.73/0.89  
% 2.73/0.89  ------ SAT Options
% 2.73/0.89  
% 2.73/0.89  --sat_mode                              false
% 2.73/0.89  --sat_fm_restart_options                ""
% 2.73/0.89  --sat_gr_def                            false
% 2.73/0.89  --sat_epr_types                         true
% 2.73/0.89  --sat_non_cyclic_types                  false
% 2.73/0.89  --sat_finite_models                     false
% 2.73/0.89  --sat_fm_lemmas                         false
% 2.73/0.89  --sat_fm_prep                           false
% 2.73/0.89  --sat_fm_uc_incr                        true
% 2.73/0.89  --sat_out_model                         small
% 2.73/0.89  --sat_out_clauses                       false
% 2.73/0.89  
% 2.73/0.89  ------ QBF Options
% 2.73/0.89  
% 2.73/0.89  --qbf_mode                              false
% 2.73/0.89  --qbf_elim_univ                         false
% 2.73/0.89  --qbf_dom_inst                          none
% 2.73/0.89  --qbf_dom_pre_inst                      false
% 2.73/0.89  --qbf_sk_in                             false
% 2.73/0.89  --qbf_pred_elim                         true
% 2.73/0.89  --qbf_split                             512
% 2.73/0.89  
% 2.73/0.89  ------ BMC1 Options
% 2.73/0.89  
% 2.73/0.89  --bmc1_incremental                      false
% 2.73/0.89  --bmc1_axioms                           reachable_all
% 2.73/0.89  --bmc1_min_bound                        0
% 2.73/0.89  --bmc1_max_bound                        -1
% 2.73/0.89  --bmc1_max_bound_default                -1
% 2.73/0.89  --bmc1_symbol_reachability              true
% 2.73/0.89  --bmc1_property_lemmas                  false
% 2.73/0.89  --bmc1_k_induction                      false
% 2.73/0.89  --bmc1_non_equiv_states                 false
% 2.73/0.89  --bmc1_deadlock                         false
% 2.73/0.89  --bmc1_ucm                              false
% 2.73/0.89  --bmc1_add_unsat_core                   none
% 2.73/0.89  --bmc1_unsat_core_children              false
% 2.73/0.89  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/0.89  --bmc1_out_stat                         full
% 2.73/0.89  --bmc1_ground_init                      false
% 2.73/0.89  --bmc1_pre_inst_next_state              false
% 2.73/0.89  --bmc1_pre_inst_state                   false
% 2.73/0.89  --bmc1_pre_inst_reach_state             false
% 2.73/0.89  --bmc1_out_unsat_core                   false
% 2.73/0.89  --bmc1_aig_witness_out                  false
% 2.73/0.89  --bmc1_verbose                          false
% 2.73/0.89  --bmc1_dump_clauses_tptp                false
% 2.73/0.89  --bmc1_dump_unsat_core_tptp             false
% 2.73/0.89  --bmc1_dump_file                        -
% 2.73/0.89  --bmc1_ucm_expand_uc_limit              128
% 2.73/0.89  --bmc1_ucm_n_expand_iterations          6
% 2.73/0.89  --bmc1_ucm_extend_mode                  1
% 2.73/0.89  --bmc1_ucm_init_mode                    2
% 2.73/0.89  --bmc1_ucm_cone_mode                    none
% 2.73/0.89  --bmc1_ucm_reduced_relation_type        0
% 2.73/0.89  --bmc1_ucm_relax_model                  4
% 2.73/0.89  --bmc1_ucm_full_tr_after_sat            true
% 2.73/0.89  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/0.89  --bmc1_ucm_layered_model                none
% 2.73/0.89  --bmc1_ucm_max_lemma_size               10
% 2.73/0.89  
% 2.73/0.89  ------ AIG Options
% 2.73/0.89  
% 2.73/0.89  --aig_mode                              false
% 2.73/0.89  
% 2.73/0.89  ------ Instantiation Options
% 2.73/0.89  
% 2.73/0.89  --instantiation_flag                    true
% 2.73/0.89  --inst_sos_flag                         false
% 2.73/0.89  --inst_sos_phase                        true
% 2.73/0.89  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/0.89  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/0.89  --inst_lit_sel_side                     none
% 2.73/0.89  --inst_solver_per_active                1400
% 2.73/0.89  --inst_solver_calls_frac                1.
% 2.73/0.89  --inst_passive_queue_type               priority_queues
% 2.73/0.89  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/0.89  --inst_passive_queues_freq              [25;2]
% 2.73/0.89  --inst_dismatching                      true
% 2.73/0.89  --inst_eager_unprocessed_to_passive     true
% 2.73/0.89  --inst_prop_sim_given                   true
% 2.73/0.89  --inst_prop_sim_new                     false
% 2.73/0.89  --inst_subs_new                         false
% 2.73/0.89  --inst_eq_res_simp                      false
% 2.73/0.89  --inst_subs_given                       false
% 2.73/0.89  --inst_orphan_elimination               true
% 2.73/0.89  --inst_learning_loop_flag               true
% 2.73/0.89  --inst_learning_start                   3000
% 2.73/0.89  --inst_learning_factor                  2
% 2.73/0.89  --inst_start_prop_sim_after_learn       3
% 2.73/0.89  --inst_sel_renew                        solver
% 2.73/0.89  --inst_lit_activity_flag                true
% 2.73/0.89  --inst_restr_to_given                   false
% 2.73/0.89  --inst_activity_threshold               500
% 2.73/0.89  --inst_out_proof                        true
% 2.73/0.89  
% 2.73/0.89  ------ Resolution Options
% 2.73/0.89  
% 2.73/0.89  --resolution_flag                       false
% 2.73/0.89  --res_lit_sel                           adaptive
% 2.73/0.89  --res_lit_sel_side                      none
% 2.73/0.89  --res_ordering                          kbo
% 2.73/0.89  --res_to_prop_solver                    active
% 2.73/0.89  --res_prop_simpl_new                    false
% 2.73/0.89  --res_prop_simpl_given                  true
% 2.73/0.89  --res_passive_queue_type                priority_queues
% 2.73/0.89  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/0.89  --res_passive_queues_freq               [15;5]
% 2.73/0.89  --res_forward_subs                      full
% 2.73/0.89  --res_backward_subs                     full
% 2.73/0.89  --res_forward_subs_resolution           true
% 2.73/0.89  --res_backward_subs_resolution          true
% 2.73/0.89  --res_orphan_elimination                true
% 2.73/0.89  --res_time_limit                        2.
% 2.73/0.89  --res_out_proof                         true
% 2.73/0.89  
% 2.73/0.89  ------ Superposition Options
% 2.73/0.89  
% 2.73/0.89  --superposition_flag                    true
% 2.73/0.89  --sup_passive_queue_type                priority_queues
% 2.73/0.89  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/0.89  --sup_passive_queues_freq               [8;1;4]
% 2.73/0.89  --demod_completeness_check              fast
% 2.73/0.89  --demod_use_ground                      true
% 2.73/0.89  --sup_to_prop_solver                    passive
% 2.73/0.89  --sup_prop_simpl_new                    true
% 2.73/0.89  --sup_prop_simpl_given                  true
% 2.73/0.89  --sup_fun_splitting                     false
% 2.73/0.89  --sup_smt_interval                      50000
% 2.73/0.89  
% 2.73/0.89  ------ Superposition Simplification Setup
% 2.73/0.89  
% 2.73/0.89  --sup_indices_passive                   []
% 2.73/0.89  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.89  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.89  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.89  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/0.89  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.89  --sup_full_bw                           [BwDemod]
% 2.73/0.89  --sup_immed_triv                        [TrivRules]
% 2.73/0.89  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/0.89  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.89  --sup_immed_bw_main                     []
% 2.73/0.89  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.89  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/0.89  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.89  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.89  
% 2.73/0.89  ------ Combination Options
% 2.73/0.89  
% 2.73/0.89  --comb_res_mult                         3
% 2.73/0.89  --comb_sup_mult                         2
% 2.73/0.89  --comb_inst_mult                        10
% 2.73/0.89  
% 2.73/0.89  ------ Debug Options
% 2.73/0.89  
% 2.73/0.89  --dbg_backtrace                         false
% 2.73/0.89  --dbg_dump_prop_clauses                 false
% 2.73/0.89  --dbg_dump_prop_clauses_file            -
% 2.73/0.89  --dbg_out_stat                          false
% 2.73/0.89  
% 2.73/0.89  
% 2.73/0.89  
% 2.73/0.89  
% 2.73/0.89  ------ Proving...
% 2.73/0.89  
% 2.73/0.89  
% 2.73/0.89  % SZS status Theorem for theBenchmark.p
% 2.73/0.89  
% 2.73/0.89  % SZS output start CNFRefutation for theBenchmark.p
% 2.73/0.89  
% 2.73/0.89  fof(f11,axiom,(
% 2.73/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.73/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.89  
% 2.73/0.89  fof(f24,plain,(
% 2.73/0.89    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.89    inference(ennf_transformation,[],[f11])).
% 2.73/0.89  
% 2.73/0.89  fof(f54,plain,(
% 2.73/0.89    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.89    inference(cnf_transformation,[],[f24])).
% 2.73/0.89  
% 2.73/0.89  fof(f13,axiom,(
% 2.73/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.73/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.89  
% 2.73/0.89  fof(f27,plain,(
% 2.73/0.89    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.89    inference(ennf_transformation,[],[f13])).
% 2.73/0.89  
% 2.73/0.89  fof(f28,plain,(
% 2.73/0.89    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.89    inference(flattening,[],[f27])).
% 2.73/0.89  
% 2.73/0.89  fof(f36,plain,(
% 2.73/0.89    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.89    inference(nnf_transformation,[],[f28])).
% 2.73/0.89  
% 2.73/0.89  fof(f56,plain,(
% 2.73/0.89    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.89    inference(cnf_transformation,[],[f36])).
% 2.73/0.89  
% 2.73/0.89  fof(f14,conjecture,(
% 2.73/0.89    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.73/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.89  
% 2.73/0.89  fof(f15,negated_conjecture,(
% 2.73/0.89    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.73/0.89    inference(negated_conjecture,[],[f14])).
% 2.73/0.89  
% 2.73/0.89  fof(f29,plain,(
% 2.73/0.89    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.73/0.89    inference(ennf_transformation,[],[f15])).
% 2.73/0.89  
% 2.73/0.89  fof(f30,plain,(
% 2.73/0.89    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.73/0.89    inference(flattening,[],[f29])).
% 2.73/0.89  
% 2.73/0.89  fof(f37,plain,(
% 2.73/0.89    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.73/0.89    introduced(choice_axiom,[])).
% 2.73/0.89  
% 2.73/0.89  fof(f38,plain,(
% 2.73/0.89    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.73/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f37])).
% 2.73/0.89  
% 2.73/0.89  fof(f63,plain,(
% 2.73/0.89    v1_funct_2(sK3,sK0,sK1)),
% 2.73/0.89    inference(cnf_transformation,[],[f38])).
% 2.73/0.89  
% 2.73/0.89  fof(f64,plain,(
% 2.73/0.89    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.73/0.89    inference(cnf_transformation,[],[f38])).
% 2.73/0.89  
% 2.73/0.89  fof(f66,plain,(
% 2.73/0.89    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 2.73/0.89    inference(cnf_transformation,[],[f38])).
% 2.73/0.89  
% 2.73/0.89  fof(f3,axiom,(
% 2.73/0.89    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.73/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.89  
% 2.73/0.89  fof(f31,plain,(
% 2.73/0.89    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.73/0.89    inference(nnf_transformation,[],[f3])).
% 2.73/0.89  
% 2.73/0.89  fof(f32,plain,(
% 2.73/0.89    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.73/0.89    inference(flattening,[],[f31])).
% 2.73/0.89  
% 2.73/0.89  fof(f41,plain,(
% 2.73/0.89    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.73/0.89    inference(cnf_transformation,[],[f32])).
% 2.73/0.89  
% 2.73/0.89  fof(f42,plain,(
% 2.73/0.89    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.73/0.89    inference(cnf_transformation,[],[f32])).
% 2.73/0.89  
% 2.73/0.89  fof(f69,plain,(
% 2.73/0.89    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.73/0.89    inference(equality_resolution,[],[f42])).
% 2.73/0.89  
% 2.73/0.89  fof(f10,axiom,(
% 2.73/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.73/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.89  
% 2.73/0.89  fof(f23,plain,(
% 2.73/0.89    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.89    inference(ennf_transformation,[],[f10])).
% 2.73/0.89  
% 2.73/0.89  fof(f52,plain,(
% 2.73/0.89    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.89    inference(cnf_transformation,[],[f23])).
% 2.73/0.89  
% 2.73/0.89  fof(f7,axiom,(
% 2.73/0.89    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.73/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.89  
% 2.73/0.89  fof(f20,plain,(
% 2.73/0.89    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.73/0.89    inference(ennf_transformation,[],[f7])).
% 2.73/0.89  
% 2.73/0.89  fof(f34,plain,(
% 2.73/0.89    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.73/0.89    inference(nnf_transformation,[],[f20])).
% 2.73/0.89  
% 2.73/0.89  fof(f47,plain,(
% 2.73/0.89    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.73/0.89    inference(cnf_transformation,[],[f34])).
% 2.73/0.89  
% 2.73/0.89  fof(f9,axiom,(
% 2.73/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.73/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.89  
% 2.73/0.89  fof(f22,plain,(
% 2.73/0.89    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.89    inference(ennf_transformation,[],[f9])).
% 2.73/0.89  
% 2.73/0.89  fof(f51,plain,(
% 2.73/0.89    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.89    inference(cnf_transformation,[],[f22])).
% 2.73/0.89  
% 2.73/0.89  fof(f2,axiom,(
% 2.73/0.89    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.73/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.89  
% 2.73/0.89  fof(f19,plain,(
% 2.73/0.89    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.73/0.89    inference(ennf_transformation,[],[f2])).
% 2.73/0.89  
% 2.73/0.89  fof(f40,plain,(
% 2.73/0.89    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.73/0.89    inference(cnf_transformation,[],[f19])).
% 2.73/0.89  
% 2.73/0.89  fof(f12,axiom,(
% 2.73/0.89    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.73/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.89  
% 2.73/0.89  fof(f25,plain,(
% 2.73/0.89    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.73/0.89    inference(ennf_transformation,[],[f12])).
% 2.73/0.89  
% 2.73/0.89  fof(f26,plain,(
% 2.73/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.73/0.89    inference(flattening,[],[f25])).
% 2.73/0.89  
% 2.73/0.89  fof(f55,plain,(
% 2.73/0.89    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.73/0.89    inference(cnf_transformation,[],[f26])).
% 2.73/0.89  
% 2.73/0.89  fof(f1,axiom,(
% 2.73/0.89    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.73/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.89  
% 2.73/0.89  fof(f17,plain,(
% 2.73/0.89    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.73/0.89    inference(ennf_transformation,[],[f1])).
% 2.73/0.89  
% 2.73/0.89  fof(f18,plain,(
% 2.73/0.89    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.73/0.89    inference(flattening,[],[f17])).
% 2.73/0.89  
% 2.73/0.89  fof(f39,plain,(
% 2.73/0.89    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.73/0.89    inference(cnf_transformation,[],[f18])).
% 2.73/0.89  
% 2.73/0.89  fof(f53,plain,(
% 2.73/0.89    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.89    inference(cnf_transformation,[],[f23])).
% 2.73/0.89  
% 2.73/0.89  fof(f8,axiom,(
% 2.73/0.89    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.73/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/0.89  
% 2.73/0.89  fof(f21,plain,(
% 2.73/0.89    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.73/0.89    inference(ennf_transformation,[],[f8])).
% 2.73/0.89  
% 2.73/0.89  fof(f35,plain,(
% 2.73/0.89    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.73/0.89    inference(nnf_transformation,[],[f21])).
% 2.73/0.89  
% 2.73/0.89  fof(f49,plain,(
% 2.73/0.89    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.73/0.89    inference(cnf_transformation,[],[f35])).
% 2.73/0.89  
% 2.73/0.89  fof(f67,plain,(
% 2.73/0.89    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 2.73/0.89    inference(cnf_transformation,[],[f38])).
% 2.73/0.89  
% 2.73/0.89  fof(f62,plain,(
% 2.73/0.89    v1_funct_1(sK3)),
% 2.73/0.89    inference(cnf_transformation,[],[f38])).
% 2.73/0.89  
% 2.73/0.89  fof(f58,plain,(
% 2.73/0.89    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.89    inference(cnf_transformation,[],[f36])).
% 2.73/0.89  
% 2.73/0.89  fof(f65,plain,(
% 2.73/0.89    r1_tarski(sK1,sK2)),
% 2.73/0.89    inference(cnf_transformation,[],[f38])).
% 2.73/0.89  
% 2.73/0.89  cnf(c_15,plain,
% 2.73/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.89      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.73/0.89      inference(cnf_transformation,[],[f54]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2661,plain,
% 2.73/0.89      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/0.89      | k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_15]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_5319,plain,
% 2.73/0.89      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.73/0.89      | k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_2661]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_750,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2909,plain,
% 2.73/0.89      ( k1_relset_1(sK0,sK2,sK3) != X0
% 2.73/0.89      | k1_relset_1(sK0,sK2,sK3) = sK0
% 2.73/0.89      | sK0 != X0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_750]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_5176,plain,
% 2.73/0.89      ( k1_relset_1(sK0,sK2,sK3) != k1_relat_1(sK3)
% 2.73/0.89      | k1_relset_1(sK0,sK2,sK3) = sK0
% 2.73/0.89      | sK0 != k1_relat_1(sK3) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_2909]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_3093,plain,
% 2.73/0.89      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_750]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_5020,plain,
% 2.73/0.89      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_3093]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_5021,plain,
% 2.73/0.89      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_5020]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1429,plain,
% 2.73/0.89      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_750]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2671,plain,
% 2.73/0.89      ( k1_relat_1(sK3) != X0 | sK0 != X0 | sK0 = k1_relat_1(sK3) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_1429]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_3405,plain,
% 2.73/0.89      ( k1_relat_1(sK3) != sK0 | sK0 = k1_relat_1(sK3) | sK0 != sK0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_2671]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_749,plain,( X0 = X0 ),theory(equality) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_3090,plain,
% 2.73/0.89      ( sK2 = sK2 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_749]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_22,plain,
% 2.73/0.89      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/0.89      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.89      | k1_relset_1(X1,X2,X0) = X1
% 2.73/0.89      | k1_xboole_0 = X2 ),
% 2.73/0.89      inference(cnf_transformation,[],[f56]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_27,negated_conjecture,
% 2.73/0.89      ( v1_funct_2(sK3,sK0,sK1) ),
% 2.73/0.89      inference(cnf_transformation,[],[f63]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_500,plain,
% 2.73/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.89      | k1_relset_1(X1,X2,X0) = X1
% 2.73/0.89      | sK1 != X2
% 2.73/0.89      | sK0 != X1
% 2.73/0.89      | sK3 != X0
% 2.73/0.89      | k1_xboole_0 = X2 ),
% 2.73/0.89      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_501,plain,
% 2.73/0.89      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.73/0.89      | k1_relset_1(sK0,sK1,sK3) = sK0
% 2.73/0.89      | k1_xboole_0 = sK1 ),
% 2.73/0.89      inference(unflattening,[status(thm)],[c_500]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_26,negated_conjecture,
% 2.73/0.89      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.73/0.89      inference(cnf_transformation,[],[f64]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_503,plain,
% 2.73/0.89      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 2.73/0.89      inference(global_propositional_subsumption,
% 2.73/0.89                [status(thm)],
% 2.73/0.89                [c_501,c_26]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1190,plain,
% 2.73/0.89      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.73/0.89      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1193,plain,
% 2.73/0.89      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.73/0.89      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.73/0.89      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2691,plain,
% 2.73/0.89      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 2.73/0.89      inference(superposition,[status(thm)],[c_1190,c_1193]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2731,plain,
% 2.73/0.89      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 2.73/0.89      inference(superposition,[status(thm)],[c_503,c_2691]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_24,negated_conjecture,
% 2.73/0.89      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 2.73/0.89      inference(cnf_transformation,[],[f66]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_4,plain,
% 2.73/0.89      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.73/0.89      | k1_xboole_0 = X0
% 2.73/0.89      | k1_xboole_0 = X1 ),
% 2.73/0.89      inference(cnf_transformation,[],[f41]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_88,plain,
% 2.73/0.89      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.73/0.89      | k1_xboole_0 = k1_xboole_0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_4]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_3,plain,
% 2.73/0.89      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.73/0.89      inference(cnf_transformation,[],[f69]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_89,plain,
% 2.73/0.89      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_3]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_14,plain,
% 2.73/0.89      ( v4_relat_1(X0,X1)
% 2.73/0.89      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.73/0.89      inference(cnf_transformation,[],[f52]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_9,plain,
% 2.73/0.89      ( ~ v4_relat_1(X0,X1)
% 2.73/0.89      | r1_tarski(k1_relat_1(X0),X1)
% 2.73/0.89      | ~ v1_relat_1(X0) ),
% 2.73/0.89      inference(cnf_transformation,[],[f47]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_346,plain,
% 2.73/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.89      | r1_tarski(k1_relat_1(X0),X1)
% 2.73/0.89      | ~ v1_relat_1(X0) ),
% 2.73/0.89      inference(resolution,[status(thm)],[c_14,c_9]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_12,plain,
% 2.73/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.89      | v1_relat_1(X0) ),
% 2.73/0.89      inference(cnf_transformation,[],[f51]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_350,plain,
% 2.73/0.89      ( r1_tarski(k1_relat_1(X0),X1)
% 2.73/0.89      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.73/0.89      inference(global_propositional_subsumption,
% 2.73/0.89                [status(thm)],
% 2.73/0.89                [c_346,c_12]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_351,plain,
% 2.73/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.89      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.73/0.89      inference(renaming,[status(thm)],[c_350]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1375,plain,
% 2.73/0.89      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.73/0.89      | r1_tarski(k1_relat_1(sK3),sK0) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_351]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1384,plain,
% 2.73/0.89      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_750]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1427,plain,
% 2.73/0.89      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_1384]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1428,plain,
% 2.73/0.89      ( sK0 = sK0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_749]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1828,plain,
% 2.73/0.89      ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_749]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_751,plain,
% 2.73/0.89      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.73/0.89      theory(equality) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1526,plain,
% 2.73/0.89      ( ~ r1_tarski(X0,X1)
% 2.73/0.89      | r1_tarski(k1_relat_1(sK3),X2)
% 2.73/0.89      | X2 != X1
% 2.73/0.89      | k1_relat_1(sK3) != X0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_751]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1827,plain,
% 2.73/0.89      ( ~ r1_tarski(k1_relat_1(sK3),X0)
% 2.73/0.89      | r1_tarski(k1_relat_1(sK3),X1)
% 2.73/0.89      | X1 != X0
% 2.73/0.89      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_1526]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2175,plain,
% 2.73/0.89      ( r1_tarski(k1_relat_1(sK3),X0)
% 2.73/0.89      | ~ r1_tarski(k1_relat_1(sK3),sK0)
% 2.73/0.89      | X0 != sK0
% 2.73/0.89      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_1827]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2177,plain,
% 2.73/0.89      ( ~ r1_tarski(k1_relat_1(sK3),sK0)
% 2.73/0.89      | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 2.73/0.89      | k1_relat_1(sK3) != k1_relat_1(sK3)
% 2.73/0.89      | k1_xboole_0 != sK0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_2175]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1831,plain,
% 2.73/0.89      ( X0 != X1 | k1_relat_1(sK3) != X1 | k1_relat_1(sK3) = X0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_750]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2183,plain,
% 2.73/0.89      ( X0 != k1_relat_1(sK3)
% 2.73/0.89      | k1_relat_1(sK3) = X0
% 2.73/0.89      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_1831]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2184,plain,
% 2.73/0.89      ( k1_relat_1(sK3) != k1_relat_1(sK3)
% 2.73/0.89      | k1_relat_1(sK3) = k1_xboole_0
% 2.73/0.89      | k1_xboole_0 != k1_relat_1(sK3) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_2183]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2227,plain,
% 2.73/0.89      ( X0 != X1 | X0 = sK1 | sK1 != X1 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_750]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2228,plain,
% 2.73/0.89      ( sK1 != k1_xboole_0
% 2.73/0.89      | k1_xboole_0 = sK1
% 2.73/0.89      | k1_xboole_0 != k1_xboole_0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_2227]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1,plain,
% 2.73/0.89      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.73/0.89      inference(cnf_transformation,[],[f40]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2656,plain,
% 2.73/0.89      ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 2.73/0.89      | k1_xboole_0 = k1_relat_1(sK3) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_1]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2670,plain,
% 2.73/0.89      ( k1_relat_1(sK3) != k1_relat_1(sK3)
% 2.73/0.89      | k1_relat_1(sK3) = sK0
% 2.73/0.89      | sK0 != k1_relat_1(sK3) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_2183]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2672,plain,
% 2.73/0.89      ( k1_relat_1(sK3) != k1_xboole_0
% 2.73/0.89      | sK0 = k1_relat_1(sK3)
% 2.73/0.89      | sK0 != k1_xboole_0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_2671]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2877,plain,
% 2.73/0.89      ( k1_relat_1(sK3) = sK0 ),
% 2.73/0.89      inference(global_propositional_subsumption,
% 2.73/0.89                [status(thm)],
% 2.73/0.89                [c_2731,c_26,c_24,c_88,c_89,c_1375,c_1427,c_1428,c_1828,
% 2.73/0.89                 c_2177,c_2184,c_2228,c_2656,c_2670,c_2672]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1732,plain,
% 2.73/0.89      ( ~ r1_tarski(X0,X1) | r1_tarski(sK1,X2) | X2 != X1 | sK1 != X0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_751]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1968,plain,
% 2.73/0.89      ( ~ r1_tarski(sK1,X0) | r1_tarski(sK1,X1) | X1 != X0 | sK1 != sK1 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_1732]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2597,plain,
% 2.73/0.89      ( r1_tarski(sK1,X0)
% 2.73/0.89      | ~ r1_tarski(sK1,sK2)
% 2.73/0.89      | X0 != sK2
% 2.73/0.89      | sK1 != sK1 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_1968]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2599,plain,
% 2.73/0.89      ( ~ r1_tarski(sK1,sK2)
% 2.73/0.89      | r1_tarski(sK1,k1_xboole_0)
% 2.73/0.89      | sK1 != sK1
% 2.73/0.89      | k1_xboole_0 != sK2 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_2597]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_16,plain,
% 2.73/0.89      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.89      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.73/0.89      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.73/0.89      | ~ v1_relat_1(X0) ),
% 2.73/0.89      inference(cnf_transformation,[],[f55]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1409,plain,
% 2.73/0.89      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/0.89      | ~ r1_tarski(k2_relat_1(sK3),X1)
% 2.73/0.89      | ~ r1_tarski(k1_relat_1(sK3),X0)
% 2.73/0.89      | ~ v1_relat_1(sK3) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_16]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1871,plain,
% 2.73/0.89      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 2.73/0.89      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 2.73/0.89      | ~ r1_tarski(k1_relat_1(sK3),X0)
% 2.73/0.89      | ~ v1_relat_1(sK3) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_1409]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2353,plain,
% 2.73/0.89      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.73/0.89      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 2.73/0.89      | ~ r1_tarski(k1_relat_1(sK3),sK0)
% 2.73/0.89      | ~ v1_relat_1(sK3) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_1871]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_2222,plain,
% 2.73/0.89      ( ~ r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_1]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_0,plain,
% 2.73/0.89      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 2.73/0.89      inference(cnf_transformation,[],[f39]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1475,plain,
% 2.73/0.89      ( ~ r1_tarski(X0,X1)
% 2.73/0.89      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 2.73/0.89      | r1_tarski(k2_relat_1(sK3),X1) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_0]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1626,plain,
% 2.73/0.89      ( r1_tarski(k2_relat_1(sK3),X0)
% 2.73/0.89      | ~ r1_tarski(k2_relat_1(sK3),sK1)
% 2.73/0.89      | ~ r1_tarski(sK1,X0) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_1475]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1729,plain,
% 2.73/0.89      ( ~ r1_tarski(k2_relat_1(sK3),sK1)
% 2.73/0.89      | r1_tarski(k2_relat_1(sK3),sK2)
% 2.73/0.89      | ~ r1_tarski(sK1,sK2) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_1626]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1432,plain,
% 2.73/0.89      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_750]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1642,plain,
% 2.73/0.89      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_1432]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1643,plain,
% 2.73/0.89      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_1642]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1608,plain,
% 2.73/0.89      ( sK3 = sK3 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_749]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1431,plain,
% 2.73/0.89      ( sK1 = sK1 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_749]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1385,plain,
% 2.73/0.89      ( sK1 != X0 | sK1 = sK2 | sK2 != X0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_750]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1386,plain,
% 2.73/0.89      ( sK1 = sK2 | sK1 != k1_xboole_0 | sK2 != k1_xboole_0 ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_1385]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_13,plain,
% 2.73/0.89      ( v5_relat_1(X0,X1)
% 2.73/0.89      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.73/0.89      inference(cnf_transformation,[],[f53]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_11,plain,
% 2.73/0.89      ( ~ v5_relat_1(X0,X1)
% 2.73/0.89      | r1_tarski(k2_relat_1(X0),X1)
% 2.73/0.89      | ~ v1_relat_1(X0) ),
% 2.73/0.89      inference(cnf_transformation,[],[f49]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_367,plain,
% 2.73/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.89      | r1_tarski(k2_relat_1(X0),X2)
% 2.73/0.89      | ~ v1_relat_1(X0) ),
% 2.73/0.89      inference(resolution,[status(thm)],[c_13,c_11]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_371,plain,
% 2.73/0.89      ( r1_tarski(k2_relat_1(X0),X2)
% 2.73/0.89      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.73/0.89      inference(global_propositional_subsumption,
% 2.73/0.89                [status(thm)],
% 2.73/0.89                [c_367,c_12]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_372,plain,
% 2.73/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.89      | r1_tarski(k2_relat_1(X0),X2) ),
% 2.73/0.89      inference(renaming,[status(thm)],[c_371]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1381,plain,
% 2.73/0.89      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.73/0.89      | r1_tarski(k2_relat_1(sK3),sK1) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_372]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_1365,plain,
% 2.73/0.89      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.73/0.89      | v1_relat_1(sK3) ),
% 2.73/0.89      inference(instantiation,[status(thm)],[c_12]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_23,negated_conjecture,
% 2.73/0.89      ( ~ v1_funct_2(sK3,sK0,sK2)
% 2.73/0.89      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.73/0.89      | ~ v1_funct_1(sK3) ),
% 2.73/0.89      inference(cnf_transformation,[],[f67]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_28,negated_conjecture,
% 2.73/0.89      ( v1_funct_1(sK3) ),
% 2.73/0.89      inference(cnf_transformation,[],[f62]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_149,plain,
% 2.73/0.89      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.73/0.89      | ~ v1_funct_2(sK3,sK0,sK2) ),
% 2.73/0.89      inference(global_propositional_subsumption,
% 2.73/0.89                [status(thm)],
% 2.73/0.89                [c_23,c_28]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_150,negated_conjecture,
% 2.73/0.89      ( ~ v1_funct_2(sK3,sK0,sK2)
% 2.73/0.89      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.73/0.89      inference(renaming,[status(thm)],[c_149]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_511,plain,
% 2.73/0.89      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.73/0.89      | sK1 != sK2
% 2.73/0.89      | sK0 != sK0
% 2.73/0.89      | sK3 != sK3 ),
% 2.73/0.89      inference(resolution_lifted,[status(thm)],[c_150,c_27]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_20,plain,
% 2.73/0.89      ( v1_funct_2(X0,X1,X2)
% 2.73/0.89      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.89      | k1_relset_1(X1,X2,X0) != X1
% 2.73/0.89      | k1_xboole_0 = X2 ),
% 2.73/0.89      inference(cnf_transformation,[],[f58]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_487,plain,
% 2.73/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.89      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.73/0.89      | k1_relset_1(X1,X2,X0) != X1
% 2.73/0.89      | sK2 != X2
% 2.73/0.89      | sK0 != X1
% 2.73/0.89      | sK3 != X0
% 2.73/0.89      | k1_xboole_0 = X2 ),
% 2.73/0.89      inference(resolution_lifted,[status(thm)],[c_20,c_150]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_488,plain,
% 2.73/0.89      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.73/0.89      | k1_relset_1(sK0,sK2,sK3) != sK0
% 2.73/0.89      | k1_xboole_0 = sK2 ),
% 2.73/0.89      inference(unflattening,[status(thm)],[c_487]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(c_25,negated_conjecture,
% 2.73/0.89      ( r1_tarski(sK1,sK2) ),
% 2.73/0.89      inference(cnf_transformation,[],[f65]) ).
% 2.73/0.89  
% 2.73/0.89  cnf(contradiction,plain,
% 2.73/0.89      ( $false ),
% 2.73/0.89      inference(minisat,
% 2.73/0.89                [status(thm)],
% 2.73/0.89                [c_5319,c_5176,c_5021,c_3405,c_3090,c_2877,c_2599,c_2353,
% 2.73/0.89                 c_2222,c_1729,c_1643,c_1608,c_1431,c_1428,c_1386,c_1381,
% 2.73/0.89                 c_1375,c_1365,c_511,c_488,c_25,c_26]) ).
% 2.73/0.89  
% 2.73/0.89  
% 2.73/0.89  % SZS output end CNFRefutation for theBenchmark.p
% 2.73/0.89  
% 2.73/0.89  ------                               Statistics
% 2.73/0.89  
% 2.73/0.89  ------ General
% 2.73/0.89  
% 2.73/0.89  abstr_ref_over_cycles:                  0
% 2.73/0.89  abstr_ref_under_cycles:                 0
% 2.73/0.89  gc_basic_clause_elim:                   0
% 2.73/0.89  forced_gc_time:                         0
% 2.73/0.89  parsing_time:                           0.008
% 2.73/0.89  unif_index_cands_time:                  0.
% 2.73/0.89  unif_index_add_time:                    0.
% 2.73/0.89  orderings_time:                         0.
% 2.73/0.89  out_proof_time:                         0.008
% 2.73/0.89  total_time:                             0.151
% 2.73/0.89  num_of_symbols:                         48
% 2.73/0.89  num_of_terms:                           3095
% 2.73/0.89  
% 2.73/0.89  ------ Preprocessing
% 2.73/0.89  
% 2.73/0.89  num_of_splits:                          0
% 2.73/0.89  num_of_split_atoms:                     0
% 2.73/0.89  num_of_reused_defs:                     0
% 2.73/0.89  num_eq_ax_congr_red:                    15
% 2.73/0.89  num_of_sem_filtered_clauses:            2
% 2.73/0.89  num_of_subtypes:                        0
% 2.73/0.89  monotx_restored_types:                  0
% 2.73/0.89  sat_num_of_epr_types:                   0
% 2.73/0.89  sat_num_of_non_cyclic_types:            0
% 2.73/0.89  sat_guarded_non_collapsed_types:        0
% 2.73/0.89  num_pure_diseq_elim:                    0
% 2.73/0.89  simp_replaced_by:                       0
% 2.73/0.89  res_preprocessed:                       113
% 2.73/0.89  prep_upred:                             0
% 2.73/0.89  prep_unflattend:                        33
% 2.73/0.89  smt_new_axioms:                         0
% 2.73/0.89  pred_elim_cands:                        3
% 2.73/0.89  pred_elim:                              3
% 2.73/0.89  pred_elim_cl:                           5
% 2.73/0.89  pred_elim_cycles:                       6
% 2.73/0.89  merged_defs:                            8
% 2.73/0.89  merged_defs_ncl:                        0
% 2.73/0.89  bin_hyper_res:                          8
% 2.73/0.89  prep_cycles:                            4
% 2.73/0.89  pred_elim_time:                         0.006
% 2.73/0.89  splitting_time:                         0.
% 2.73/0.89  sem_filter_time:                        0.
% 2.73/0.89  monotx_time:                            0.
% 2.73/0.89  subtype_inf_time:                       0.
% 2.73/0.89  
% 2.73/0.89  ------ Problem properties
% 2.73/0.89  
% 2.73/0.89  clauses:                                23
% 2.73/0.89  conjectures:                            3
% 2.73/0.89  epr:                                    4
% 2.73/0.89  horn:                                   20
% 2.73/0.89  ground:                                 10
% 2.73/0.89  unary:                                  5
% 2.73/0.89  binary:                                 10
% 2.73/0.89  lits:                                   53
% 2.73/0.89  lits_eq:                                24
% 2.73/0.89  fd_pure:                                0
% 2.73/0.89  fd_pseudo:                              0
% 2.73/0.89  fd_cond:                                2
% 2.73/0.89  fd_pseudo_cond:                         0
% 2.73/0.89  ac_symbols:                             0
% 2.73/0.89  
% 2.73/0.89  ------ Propositional Solver
% 2.73/0.89  
% 2.73/0.89  prop_solver_calls:                      30
% 2.73/0.89  prop_fast_solver_calls:                 764
% 2.73/0.89  smt_solver_calls:                       0
% 2.73/0.89  smt_fast_solver_calls:                  0
% 2.73/0.89  prop_num_of_clauses:                    1699
% 2.73/0.89  prop_preprocess_simplified:             5091
% 2.73/0.89  prop_fo_subsumed:                       7
% 2.73/0.89  prop_solver_time:                       0.
% 2.73/0.89  smt_solver_time:                        0.
% 2.73/0.89  smt_fast_solver_time:                   0.
% 2.73/0.89  prop_fast_solver_time:                  0.
% 2.73/0.89  prop_unsat_core_time:                   0.
% 2.73/0.89  
% 2.73/0.89  ------ QBF
% 2.73/0.89  
% 2.73/0.89  qbf_q_res:                              0
% 2.73/0.89  qbf_num_tautologies:                    0
% 2.73/0.89  qbf_prep_cycles:                        0
% 2.73/0.89  
% 2.73/0.89  ------ BMC1
% 2.73/0.89  
% 2.73/0.89  bmc1_current_bound:                     -1
% 2.73/0.89  bmc1_last_solved_bound:                 -1
% 2.73/0.89  bmc1_unsat_core_size:                   -1
% 2.73/0.89  bmc1_unsat_core_parents_size:           -1
% 2.73/0.89  bmc1_merge_next_fun:                    0
% 2.73/0.89  bmc1_unsat_core_clauses_time:           0.
% 2.73/0.89  
% 2.73/0.89  ------ Instantiation
% 2.73/0.89  
% 2.73/0.89  inst_num_of_clauses:                    557
% 2.73/0.89  inst_num_in_passive:                    202
% 2.73/0.89  inst_num_in_active:                     336
% 2.73/0.89  inst_num_in_unprocessed:                18
% 2.73/0.89  inst_num_of_loops:                      424
% 2.73/0.89  inst_num_of_learning_restarts:          0
% 2.73/0.89  inst_num_moves_active_passive:          82
% 2.73/0.89  inst_lit_activity:                      0
% 2.73/0.89  inst_lit_activity_moves:                0
% 2.73/0.89  inst_num_tautologies:                   0
% 2.73/0.89  inst_num_prop_implied:                  0
% 2.73/0.89  inst_num_existing_simplified:           0
% 2.73/0.89  inst_num_eq_res_simplified:             0
% 2.73/0.89  inst_num_child_elim:                    0
% 2.73/0.89  inst_num_of_dismatching_blockings:      212
% 2.73/0.89  inst_num_of_non_proper_insts:           758
% 2.73/0.89  inst_num_of_duplicates:                 0
% 2.73/0.89  inst_inst_num_from_inst_to_res:         0
% 2.73/0.89  inst_dismatching_checking_time:         0.
% 2.73/0.89  
% 2.73/0.89  ------ Resolution
% 2.73/0.89  
% 2.73/0.89  res_num_of_clauses:                     0
% 2.73/0.89  res_num_in_passive:                     0
% 2.73/0.89  res_num_in_active:                      0
% 2.73/0.89  res_num_of_loops:                       117
% 2.73/0.89  res_forward_subset_subsumed:            18
% 2.73/0.89  res_backward_subset_subsumed:           0
% 2.73/0.89  res_forward_subsumed:                   0
% 2.73/0.89  res_backward_subsumed:                  0
% 2.73/0.89  res_forward_subsumption_resolution:     1
% 2.73/0.89  res_backward_subsumption_resolution:    0
% 2.73/0.89  res_clause_to_clause_subsumption:       514
% 2.73/0.89  res_orphan_elimination:                 0
% 2.73/0.89  res_tautology_del:                      113
% 2.73/0.89  res_num_eq_res_simplified:              1
% 2.73/0.89  res_num_sel_changes:                    0
% 2.73/0.89  res_moves_from_active_to_pass:          0
% 2.73/0.89  
% 2.73/0.89  ------ Superposition
% 2.73/0.89  
% 2.73/0.89  sup_time_total:                         0.
% 2.73/0.89  sup_time_generating:                    0.
% 2.73/0.89  sup_time_sim_full:                      0.
% 2.73/0.89  sup_time_sim_immed:                     0.
% 2.73/0.89  
% 2.73/0.89  sup_num_of_clauses:                     133
% 2.73/0.89  sup_num_in_active:                      79
% 2.73/0.89  sup_num_in_passive:                     54
% 2.73/0.89  sup_num_of_loops:                       84
% 2.73/0.89  sup_fw_superposition:                   107
% 2.73/0.89  sup_bw_superposition:                   80
% 2.73/0.89  sup_immediate_simplified:               41
% 2.73/0.89  sup_given_eliminated:                   0
% 2.73/0.89  comparisons_done:                       0
% 2.73/0.89  comparisons_avoided:                    0
% 2.73/0.89  
% 2.73/0.89  ------ Simplifications
% 2.73/0.89  
% 2.73/0.89  
% 2.73/0.89  sim_fw_subset_subsumed:                 8
% 2.73/0.89  sim_bw_subset_subsumed:                 1
% 2.73/0.89  sim_fw_subsumed:                        22
% 2.73/0.89  sim_bw_subsumed:                        2
% 2.73/0.89  sim_fw_subsumption_res:                 0
% 2.73/0.89  sim_bw_subsumption_res:                 0
% 2.73/0.89  sim_tautology_del:                      7
% 2.73/0.89  sim_eq_tautology_del:                   4
% 2.73/0.89  sim_eq_res_simp:                        0
% 2.73/0.89  sim_fw_demodulated:                     3
% 2.73/0.89  sim_bw_demodulated:                     4
% 2.73/0.89  sim_light_normalised:                   15
% 2.73/0.89  sim_joinable_taut:                      0
% 2.73/0.89  sim_joinable_simp:                      0
% 2.73/0.89  sim_ac_normalised:                      0
% 2.73/0.89  sim_smt_subsumption:                    0
% 2.73/0.89  
%------------------------------------------------------------------------------
