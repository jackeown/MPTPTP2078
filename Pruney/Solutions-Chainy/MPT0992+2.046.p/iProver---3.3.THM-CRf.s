%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:55 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  182 (6117 expanded)
%              Number of clauses        :  122 (2026 expanded)
%              Number of leaves         :   15 (1144 expanded)
%              Depth                    :   26
%              Number of atoms          :  563 (34126 expanded)
%              Number of equality atoms :  301 (9133 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f40])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f26])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f56])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1803,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1806,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3887,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1803,c_1806])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2106,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2259,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2106])).

cnf(c_3995,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3887,c_30,c_28,c_2259])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1808,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5081,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3995,c_1808])).

cnf(c_31,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5657,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5081,c_31,c_33])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_10])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_331,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_327,c_9])).

cnf(c_332,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_331])).

cnf(c_1800,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_5667,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5657,c_1800])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1804,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_683,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_684,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_683])).

cnf(c_686,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_684,c_28])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1809,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2726,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1803,c_1809])).

cnf(c_2916,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_686,c_2726])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1811,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2975,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2916,c_1811])).

cnf(c_2043,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2044,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2043])).

cnf(c_2980,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2975,c_33,c_2044])).

cnf(c_2981,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2980])).

cnf(c_2989,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1804,c_2981])).

cnf(c_22,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1805,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4122,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2989,c_1805])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1807,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3237,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1803,c_1807])).

cnf(c_2086,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2251,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2086])).

cnf(c_2252,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2251])).

cnf(c_3670,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3237,c_31,c_33,c_2252])).

cnf(c_4004,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3995,c_3670])).

cnf(c_4641,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4122,c_4004])).

cnf(c_23,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_694,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_25])).

cnf(c_695,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_707,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_695,c_9,c_332])).

cnf(c_1791,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_707])).

cnf(c_4002,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3995,c_1791])).

cnf(c_4018,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4002,c_4004])).

cnf(c_4712,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2989,c_4018])).

cnf(c_4848,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4641,c_4712])).

cnf(c_5756,plain,
    ( sK1 = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5667,c_4848])).

cnf(c_1810,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5670,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5657,c_1810])).

cnf(c_6647,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5756,c_5670])).

cnf(c_6655,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6647,c_5657])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_6670,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6647,c_26])).

cnf(c_6671,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6670])).

cnf(c_6704,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6655,c_6671])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_6706,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6704,c_2])).

cnf(c_6657,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6647,c_4018])).

cnf(c_1,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_6696,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6657,c_1])).

cnf(c_6708,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_6706,c_6696])).

cnf(c_6665,plain,
    ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_6647,c_2726])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_628,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_627])).

cnf(c_1794,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_628])).

cnf(c_1868,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1794,c_2])).

cnf(c_6667,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6647,c_1868])).

cnf(c_6678,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6667,c_6671])).

cnf(c_6679,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6678])).

cnf(c_6669,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6647,c_1803])).

cnf(c_6674,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6669,c_6671])).

cnf(c_6676,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6674,c_2])).

cnf(c_6682,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6679,c_6676])).

cnf(c_6685,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6665,c_6671,c_6682])).

cnf(c_1369,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2407,plain,
    ( X0 != X1
    | X0 = sK0
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_3447,plain,
    ( k1_relat_1(sK3) != X0
    | k1_relat_1(sK3) = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_2407])).

cnf(c_3448,plain,
    ( k1_relat_1(sK3) = sK0
    | k1_relat_1(sK3) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3447])).

cnf(c_2119,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2813,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_2119])).

cnf(c_1370,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2091,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK2,sK0)
    | X0 != sK2
    | X1 != sK0 ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_2192,plain,
    ( r1_tarski(sK2,X0)
    | ~ r1_tarski(sK2,sK0)
    | X0 != sK0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2091])).

cnf(c_2812,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3))
    | ~ r1_tarski(sK2,sK0)
    | k1_relat_1(sK3) != sK0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2192])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X0
    | sK1 != k1_xboole_0
    | sK0 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_564,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_563])).

cnf(c_1797,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_1875,plain,
    ( sK3 = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1797,c_1])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_97,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_98,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2058,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_2331,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2058])).

cnf(c_1368,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2332,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_2423,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_2424,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2423])).

cnf(c_2437,plain,
    ( sK0 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1875,c_26,c_97,c_98,c_2331,c_2332,c_2424])).

cnf(c_2438,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2437])).

cnf(c_2193,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6708,c_6685,c_6647,c_3448,c_2813,c_2812,c_2438,c_2193,c_2043,c_27,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.01/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.02  
% 3.01/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/1.02  
% 3.01/1.02  ------  iProver source info
% 3.01/1.02  
% 3.01/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.01/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/1.02  git: non_committed_changes: false
% 3.01/1.02  git: last_make_outside_of_git: false
% 3.01/1.02  
% 3.01/1.02  ------ 
% 3.01/1.02  
% 3.01/1.02  ------ Input Options
% 3.01/1.02  
% 3.01/1.02  --out_options                           all
% 3.01/1.02  --tptp_safe_out                         true
% 3.01/1.02  --problem_path                          ""
% 3.01/1.02  --include_path                          ""
% 3.01/1.02  --clausifier                            res/vclausify_rel
% 3.01/1.02  --clausifier_options                    --mode clausify
% 3.01/1.02  --stdin                                 false
% 3.01/1.02  --stats_out                             all
% 3.01/1.02  
% 3.01/1.02  ------ General Options
% 3.01/1.02  
% 3.01/1.02  --fof                                   false
% 3.01/1.02  --time_out_real                         305.
% 3.01/1.02  --time_out_virtual                      -1.
% 3.01/1.02  --symbol_type_check                     false
% 3.01/1.02  --clausify_out                          false
% 3.01/1.02  --sig_cnt_out                           false
% 3.01/1.02  --trig_cnt_out                          false
% 3.01/1.02  --trig_cnt_out_tolerance                1.
% 3.01/1.02  --trig_cnt_out_sk_spl                   false
% 3.01/1.02  --abstr_cl_out                          false
% 3.01/1.02  
% 3.01/1.02  ------ Global Options
% 3.01/1.02  
% 3.01/1.02  --schedule                              default
% 3.01/1.02  --add_important_lit                     false
% 3.01/1.02  --prop_solver_per_cl                    1000
% 3.01/1.02  --min_unsat_core                        false
% 3.01/1.02  --soft_assumptions                      false
% 3.01/1.02  --soft_lemma_size                       3
% 3.01/1.02  --prop_impl_unit_size                   0
% 3.01/1.02  --prop_impl_unit                        []
% 3.01/1.02  --share_sel_clauses                     true
% 3.01/1.02  --reset_solvers                         false
% 3.01/1.02  --bc_imp_inh                            [conj_cone]
% 3.01/1.02  --conj_cone_tolerance                   3.
% 3.01/1.02  --extra_neg_conj                        none
% 3.01/1.02  --large_theory_mode                     true
% 3.01/1.02  --prolific_symb_bound                   200
% 3.01/1.02  --lt_threshold                          2000
% 3.01/1.02  --clause_weak_htbl                      true
% 3.01/1.02  --gc_record_bc_elim                     false
% 3.01/1.02  
% 3.01/1.02  ------ Preprocessing Options
% 3.01/1.02  
% 3.01/1.02  --preprocessing_flag                    true
% 3.01/1.02  --time_out_prep_mult                    0.1
% 3.01/1.02  --splitting_mode                        input
% 3.01/1.02  --splitting_grd                         true
% 3.01/1.02  --splitting_cvd                         false
% 3.01/1.02  --splitting_cvd_svl                     false
% 3.01/1.02  --splitting_nvd                         32
% 3.01/1.02  --sub_typing                            true
% 3.01/1.02  --prep_gs_sim                           true
% 3.01/1.02  --prep_unflatten                        true
% 3.01/1.02  --prep_res_sim                          true
% 3.01/1.02  --prep_upred                            true
% 3.01/1.02  --prep_sem_filter                       exhaustive
% 3.01/1.02  --prep_sem_filter_out                   false
% 3.01/1.02  --pred_elim                             true
% 3.01/1.02  --res_sim_input                         true
% 3.01/1.02  --eq_ax_congr_red                       true
% 3.01/1.02  --pure_diseq_elim                       true
% 3.01/1.02  --brand_transform                       false
% 3.01/1.02  --non_eq_to_eq                          false
% 3.01/1.02  --prep_def_merge                        true
% 3.01/1.02  --prep_def_merge_prop_impl              false
% 3.01/1.02  --prep_def_merge_mbd                    true
% 3.01/1.02  --prep_def_merge_tr_red                 false
% 3.01/1.02  --prep_def_merge_tr_cl                  false
% 3.01/1.02  --smt_preprocessing                     true
% 3.01/1.02  --smt_ac_axioms                         fast
% 3.01/1.02  --preprocessed_out                      false
% 3.01/1.02  --preprocessed_stats                    false
% 3.01/1.02  
% 3.01/1.02  ------ Abstraction refinement Options
% 3.01/1.02  
% 3.01/1.02  --abstr_ref                             []
% 3.01/1.02  --abstr_ref_prep                        false
% 3.01/1.02  --abstr_ref_until_sat                   false
% 3.01/1.02  --abstr_ref_sig_restrict                funpre
% 3.01/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/1.02  --abstr_ref_under                       []
% 3.01/1.02  
% 3.01/1.02  ------ SAT Options
% 3.01/1.02  
% 3.01/1.02  --sat_mode                              false
% 3.01/1.02  --sat_fm_restart_options                ""
% 3.01/1.02  --sat_gr_def                            false
% 3.01/1.02  --sat_epr_types                         true
% 3.01/1.02  --sat_non_cyclic_types                  false
% 3.01/1.02  --sat_finite_models                     false
% 3.01/1.02  --sat_fm_lemmas                         false
% 3.01/1.02  --sat_fm_prep                           false
% 3.01/1.02  --sat_fm_uc_incr                        true
% 3.01/1.02  --sat_out_model                         small
% 3.01/1.02  --sat_out_clauses                       false
% 3.01/1.02  
% 3.01/1.02  ------ QBF Options
% 3.01/1.02  
% 3.01/1.02  --qbf_mode                              false
% 3.01/1.02  --qbf_elim_univ                         false
% 3.01/1.02  --qbf_dom_inst                          none
% 3.01/1.02  --qbf_dom_pre_inst                      false
% 3.01/1.02  --qbf_sk_in                             false
% 3.01/1.02  --qbf_pred_elim                         true
% 3.01/1.02  --qbf_split                             512
% 3.01/1.02  
% 3.01/1.02  ------ BMC1 Options
% 3.01/1.02  
% 3.01/1.02  --bmc1_incremental                      false
% 3.01/1.02  --bmc1_axioms                           reachable_all
% 3.01/1.02  --bmc1_min_bound                        0
% 3.01/1.02  --bmc1_max_bound                        -1
% 3.01/1.02  --bmc1_max_bound_default                -1
% 3.01/1.02  --bmc1_symbol_reachability              true
% 3.01/1.02  --bmc1_property_lemmas                  false
% 3.01/1.02  --bmc1_k_induction                      false
% 3.01/1.02  --bmc1_non_equiv_states                 false
% 3.01/1.02  --bmc1_deadlock                         false
% 3.01/1.02  --bmc1_ucm                              false
% 3.01/1.02  --bmc1_add_unsat_core                   none
% 3.01/1.02  --bmc1_unsat_core_children              false
% 3.01/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/1.02  --bmc1_out_stat                         full
% 3.01/1.02  --bmc1_ground_init                      false
% 3.01/1.02  --bmc1_pre_inst_next_state              false
% 3.01/1.02  --bmc1_pre_inst_state                   false
% 3.01/1.02  --bmc1_pre_inst_reach_state             false
% 3.01/1.02  --bmc1_out_unsat_core                   false
% 3.01/1.02  --bmc1_aig_witness_out                  false
% 3.01/1.02  --bmc1_verbose                          false
% 3.01/1.02  --bmc1_dump_clauses_tptp                false
% 3.01/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.01/1.02  --bmc1_dump_file                        -
% 3.01/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.02  --bmc1_ucm_extend_mode                  1
% 3.01/1.02  --bmc1_ucm_init_mode                    2
% 3.01/1.02  --bmc1_ucm_cone_mode                    none
% 3.01/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.02  --bmc1_ucm_relax_model                  4
% 3.01/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.02  --bmc1_ucm_layered_model                none
% 3.01/1.02  --bmc1_ucm_max_lemma_size               10
% 3.01/1.02  
% 3.01/1.02  ------ AIG Options
% 3.01/1.02  
% 3.01/1.02  --aig_mode                              false
% 3.01/1.02  
% 3.01/1.02  ------ Instantiation Options
% 3.01/1.02  
% 3.01/1.02  --instantiation_flag                    true
% 3.01/1.02  --inst_sos_flag                         false
% 3.01/1.02  --inst_sos_phase                        true
% 3.01/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.02  --inst_lit_sel_side                     num_symb
% 3.01/1.02  --inst_solver_per_active                1400
% 3.01/1.02  --inst_solver_calls_frac                1.
% 3.01/1.02  --inst_passive_queue_type               priority_queues
% 3.01/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/1.02  --inst_passive_queues_freq              [25;2]
% 3.01/1.02  --inst_dismatching                      true
% 3.01/1.02  --inst_eager_unprocessed_to_passive     true
% 3.01/1.02  --inst_prop_sim_given                   true
% 3.01/1.02  --inst_prop_sim_new                     false
% 3.01/1.02  --inst_subs_new                         false
% 3.01/1.02  --inst_eq_res_simp                      false
% 3.01/1.02  --inst_subs_given                       false
% 3.01/1.02  --inst_orphan_elimination               true
% 3.01/1.02  --inst_learning_loop_flag               true
% 3.01/1.02  --inst_learning_start                   3000
% 3.01/1.02  --inst_learning_factor                  2
% 3.01/1.02  --inst_start_prop_sim_after_learn       3
% 3.01/1.02  --inst_sel_renew                        solver
% 3.01/1.02  --inst_lit_activity_flag                true
% 3.01/1.02  --inst_restr_to_given                   false
% 3.01/1.02  --inst_activity_threshold               500
% 3.01/1.02  --inst_out_proof                        true
% 3.01/1.02  
% 3.01/1.02  ------ Resolution Options
% 3.01/1.02  
% 3.01/1.02  --resolution_flag                       true
% 3.01/1.02  --res_lit_sel                           adaptive
% 3.01/1.02  --res_lit_sel_side                      none
% 3.01/1.02  --res_ordering                          kbo
% 3.01/1.02  --res_to_prop_solver                    active
% 3.01/1.02  --res_prop_simpl_new                    false
% 3.01/1.02  --res_prop_simpl_given                  true
% 3.01/1.02  --res_passive_queue_type                priority_queues
% 3.01/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/1.02  --res_passive_queues_freq               [15;5]
% 3.01/1.02  --res_forward_subs                      full
% 3.01/1.02  --res_backward_subs                     full
% 3.01/1.02  --res_forward_subs_resolution           true
% 3.01/1.02  --res_backward_subs_resolution          true
% 3.01/1.02  --res_orphan_elimination                true
% 3.01/1.02  --res_time_limit                        2.
% 3.01/1.02  --res_out_proof                         true
% 3.01/1.02  
% 3.01/1.02  ------ Superposition Options
% 3.01/1.02  
% 3.01/1.02  --superposition_flag                    true
% 3.01/1.02  --sup_passive_queue_type                priority_queues
% 3.01/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.02  --demod_completeness_check              fast
% 3.01/1.02  --demod_use_ground                      true
% 3.01/1.02  --sup_to_prop_solver                    passive
% 3.01/1.02  --sup_prop_simpl_new                    true
% 3.01/1.02  --sup_prop_simpl_given                  true
% 3.01/1.02  --sup_fun_splitting                     false
% 3.01/1.02  --sup_smt_interval                      50000
% 3.01/1.02  
% 3.01/1.02  ------ Superposition Simplification Setup
% 3.01/1.02  
% 3.01/1.02  --sup_indices_passive                   []
% 3.01/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.02  --sup_full_bw                           [BwDemod]
% 3.01/1.02  --sup_immed_triv                        [TrivRules]
% 3.01/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.02  --sup_immed_bw_main                     []
% 3.01/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.02  
% 3.01/1.02  ------ Combination Options
% 3.01/1.02  
% 3.01/1.02  --comb_res_mult                         3
% 3.01/1.02  --comb_sup_mult                         2
% 3.01/1.02  --comb_inst_mult                        10
% 3.01/1.02  
% 3.01/1.02  ------ Debug Options
% 3.01/1.02  
% 3.01/1.02  --dbg_backtrace                         false
% 3.01/1.02  --dbg_dump_prop_clauses                 false
% 3.01/1.02  --dbg_dump_prop_clauses_file            -
% 3.01/1.02  --dbg_out_stat                          false
% 3.01/1.02  ------ Parsing...
% 3.01/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/1.02  
% 3.01/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.01/1.02  
% 3.01/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/1.02  
% 3.01/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.02  ------ Proving...
% 3.01/1.02  ------ Problem Properties 
% 3.01/1.02  
% 3.01/1.02  
% 3.01/1.02  clauses                                 29
% 3.01/1.02  conjectures                             4
% 3.01/1.02  EPR                                     4
% 3.01/1.02  Horn                                    24
% 3.01/1.02  unary                                   5
% 3.01/1.02  binary                                  8
% 3.01/1.02  lits                                    83
% 3.01/1.02  lits eq                                 35
% 3.01/1.02  fd_pure                                 0
% 3.01/1.02  fd_pseudo                               0
% 3.01/1.02  fd_cond                                 4
% 3.01/1.02  fd_pseudo_cond                          0
% 3.01/1.02  AC symbols                              0
% 3.01/1.02  
% 3.01/1.02  ------ Schedule dynamic 5 is on 
% 3.01/1.02  
% 3.01/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.01/1.02  
% 3.01/1.02  
% 3.01/1.02  ------ 
% 3.01/1.02  Current options:
% 3.01/1.02  ------ 
% 3.01/1.02  
% 3.01/1.02  ------ Input Options
% 3.01/1.02  
% 3.01/1.02  --out_options                           all
% 3.01/1.02  --tptp_safe_out                         true
% 3.01/1.02  --problem_path                          ""
% 3.01/1.02  --include_path                          ""
% 3.01/1.02  --clausifier                            res/vclausify_rel
% 3.01/1.02  --clausifier_options                    --mode clausify
% 3.01/1.02  --stdin                                 false
% 3.01/1.02  --stats_out                             all
% 3.01/1.02  
% 3.01/1.02  ------ General Options
% 3.01/1.02  
% 3.01/1.02  --fof                                   false
% 3.01/1.02  --time_out_real                         305.
% 3.01/1.02  --time_out_virtual                      -1.
% 3.01/1.02  --symbol_type_check                     false
% 3.01/1.02  --clausify_out                          false
% 3.01/1.02  --sig_cnt_out                           false
% 3.01/1.02  --trig_cnt_out                          false
% 3.01/1.02  --trig_cnt_out_tolerance                1.
% 3.01/1.02  --trig_cnt_out_sk_spl                   false
% 3.01/1.02  --abstr_cl_out                          false
% 3.01/1.02  
% 3.01/1.02  ------ Global Options
% 3.01/1.02  
% 3.01/1.02  --schedule                              default
% 3.01/1.02  --add_important_lit                     false
% 3.01/1.02  --prop_solver_per_cl                    1000
% 3.01/1.02  --min_unsat_core                        false
% 3.01/1.02  --soft_assumptions                      false
% 3.01/1.02  --soft_lemma_size                       3
% 3.01/1.02  --prop_impl_unit_size                   0
% 3.01/1.02  --prop_impl_unit                        []
% 3.01/1.02  --share_sel_clauses                     true
% 3.01/1.02  --reset_solvers                         false
% 3.01/1.02  --bc_imp_inh                            [conj_cone]
% 3.01/1.02  --conj_cone_tolerance                   3.
% 3.01/1.02  --extra_neg_conj                        none
% 3.01/1.02  --large_theory_mode                     true
% 3.01/1.02  --prolific_symb_bound                   200
% 3.01/1.02  --lt_threshold                          2000
% 3.01/1.02  --clause_weak_htbl                      true
% 3.01/1.02  --gc_record_bc_elim                     false
% 3.01/1.02  
% 3.01/1.02  ------ Preprocessing Options
% 3.01/1.02  
% 3.01/1.02  --preprocessing_flag                    true
% 3.01/1.02  --time_out_prep_mult                    0.1
% 3.01/1.02  --splitting_mode                        input
% 3.01/1.02  --splitting_grd                         true
% 3.01/1.02  --splitting_cvd                         false
% 3.01/1.02  --splitting_cvd_svl                     false
% 3.01/1.02  --splitting_nvd                         32
% 3.01/1.02  --sub_typing                            true
% 3.01/1.02  --prep_gs_sim                           true
% 3.01/1.02  --prep_unflatten                        true
% 3.01/1.02  --prep_res_sim                          true
% 3.01/1.02  --prep_upred                            true
% 3.01/1.02  --prep_sem_filter                       exhaustive
% 3.01/1.02  --prep_sem_filter_out                   false
% 3.01/1.02  --pred_elim                             true
% 3.01/1.02  --res_sim_input                         true
% 3.01/1.02  --eq_ax_congr_red                       true
% 3.01/1.02  --pure_diseq_elim                       true
% 3.01/1.02  --brand_transform                       false
% 3.01/1.02  --non_eq_to_eq                          false
% 3.01/1.02  --prep_def_merge                        true
% 3.01/1.02  --prep_def_merge_prop_impl              false
% 3.01/1.02  --prep_def_merge_mbd                    true
% 3.01/1.02  --prep_def_merge_tr_red                 false
% 3.01/1.02  --prep_def_merge_tr_cl                  false
% 3.01/1.02  --smt_preprocessing                     true
% 3.01/1.02  --smt_ac_axioms                         fast
% 3.01/1.02  --preprocessed_out                      false
% 3.01/1.02  --preprocessed_stats                    false
% 3.01/1.02  
% 3.01/1.02  ------ Abstraction refinement Options
% 3.01/1.02  
% 3.01/1.02  --abstr_ref                             []
% 3.01/1.02  --abstr_ref_prep                        false
% 3.01/1.02  --abstr_ref_until_sat                   false
% 3.01/1.02  --abstr_ref_sig_restrict                funpre
% 3.01/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/1.02  --abstr_ref_under                       []
% 3.01/1.02  
% 3.01/1.02  ------ SAT Options
% 3.01/1.02  
% 3.01/1.02  --sat_mode                              false
% 3.01/1.02  --sat_fm_restart_options                ""
% 3.01/1.02  --sat_gr_def                            false
% 3.01/1.02  --sat_epr_types                         true
% 3.01/1.02  --sat_non_cyclic_types                  false
% 3.01/1.02  --sat_finite_models                     false
% 3.01/1.02  --sat_fm_lemmas                         false
% 3.01/1.02  --sat_fm_prep                           false
% 3.01/1.02  --sat_fm_uc_incr                        true
% 3.01/1.02  --sat_out_model                         small
% 3.01/1.02  --sat_out_clauses                       false
% 3.01/1.02  
% 3.01/1.02  ------ QBF Options
% 3.01/1.02  
% 3.01/1.02  --qbf_mode                              false
% 3.01/1.02  --qbf_elim_univ                         false
% 3.01/1.02  --qbf_dom_inst                          none
% 3.01/1.02  --qbf_dom_pre_inst                      false
% 3.01/1.02  --qbf_sk_in                             false
% 3.01/1.02  --qbf_pred_elim                         true
% 3.01/1.02  --qbf_split                             512
% 3.01/1.02  
% 3.01/1.02  ------ BMC1 Options
% 3.01/1.02  
% 3.01/1.02  --bmc1_incremental                      false
% 3.01/1.02  --bmc1_axioms                           reachable_all
% 3.01/1.02  --bmc1_min_bound                        0
% 3.01/1.02  --bmc1_max_bound                        -1
% 3.01/1.02  --bmc1_max_bound_default                -1
% 3.01/1.02  --bmc1_symbol_reachability              true
% 3.01/1.02  --bmc1_property_lemmas                  false
% 3.01/1.02  --bmc1_k_induction                      false
% 3.01/1.02  --bmc1_non_equiv_states                 false
% 3.01/1.02  --bmc1_deadlock                         false
% 3.01/1.02  --bmc1_ucm                              false
% 3.01/1.02  --bmc1_add_unsat_core                   none
% 3.01/1.02  --bmc1_unsat_core_children              false
% 3.01/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/1.02  --bmc1_out_stat                         full
% 3.01/1.02  --bmc1_ground_init                      false
% 3.01/1.02  --bmc1_pre_inst_next_state              false
% 3.01/1.02  --bmc1_pre_inst_state                   false
% 3.01/1.02  --bmc1_pre_inst_reach_state             false
% 3.01/1.02  --bmc1_out_unsat_core                   false
% 3.01/1.02  --bmc1_aig_witness_out                  false
% 3.01/1.02  --bmc1_verbose                          false
% 3.01/1.02  --bmc1_dump_clauses_tptp                false
% 3.01/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.01/1.02  --bmc1_dump_file                        -
% 3.01/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.02  --bmc1_ucm_extend_mode                  1
% 3.01/1.02  --bmc1_ucm_init_mode                    2
% 3.01/1.02  --bmc1_ucm_cone_mode                    none
% 3.01/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.02  --bmc1_ucm_relax_model                  4
% 3.01/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.02  --bmc1_ucm_layered_model                none
% 3.01/1.02  --bmc1_ucm_max_lemma_size               10
% 3.01/1.02  
% 3.01/1.02  ------ AIG Options
% 3.01/1.02  
% 3.01/1.02  --aig_mode                              false
% 3.01/1.02  
% 3.01/1.02  ------ Instantiation Options
% 3.01/1.02  
% 3.01/1.02  --instantiation_flag                    true
% 3.01/1.02  --inst_sos_flag                         false
% 3.01/1.02  --inst_sos_phase                        true
% 3.01/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.02  --inst_lit_sel_side                     none
% 3.01/1.02  --inst_solver_per_active                1400
% 3.01/1.02  --inst_solver_calls_frac                1.
% 3.01/1.02  --inst_passive_queue_type               priority_queues
% 3.01/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/1.02  --inst_passive_queues_freq              [25;2]
% 3.01/1.02  --inst_dismatching                      true
% 3.01/1.02  --inst_eager_unprocessed_to_passive     true
% 3.01/1.02  --inst_prop_sim_given                   true
% 3.01/1.02  --inst_prop_sim_new                     false
% 3.01/1.02  --inst_subs_new                         false
% 3.01/1.02  --inst_eq_res_simp                      false
% 3.01/1.02  --inst_subs_given                       false
% 3.01/1.02  --inst_orphan_elimination               true
% 3.01/1.02  --inst_learning_loop_flag               true
% 3.01/1.02  --inst_learning_start                   3000
% 3.01/1.02  --inst_learning_factor                  2
% 3.01/1.02  --inst_start_prop_sim_after_learn       3
% 3.01/1.02  --inst_sel_renew                        solver
% 3.01/1.02  --inst_lit_activity_flag                true
% 3.01/1.02  --inst_restr_to_given                   false
% 3.01/1.02  --inst_activity_threshold               500
% 3.01/1.02  --inst_out_proof                        true
% 3.01/1.02  
% 3.01/1.02  ------ Resolution Options
% 3.01/1.02  
% 3.01/1.02  --resolution_flag                       false
% 3.01/1.02  --res_lit_sel                           adaptive
% 3.01/1.02  --res_lit_sel_side                      none
% 3.01/1.02  --res_ordering                          kbo
% 3.01/1.02  --res_to_prop_solver                    active
% 3.01/1.02  --res_prop_simpl_new                    false
% 3.01/1.02  --res_prop_simpl_given                  true
% 3.01/1.02  --res_passive_queue_type                priority_queues
% 3.01/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/1.02  --res_passive_queues_freq               [15;5]
% 3.01/1.02  --res_forward_subs                      full
% 3.01/1.02  --res_backward_subs                     full
% 3.01/1.02  --res_forward_subs_resolution           true
% 3.01/1.02  --res_backward_subs_resolution          true
% 3.01/1.02  --res_orphan_elimination                true
% 3.01/1.02  --res_time_limit                        2.
% 3.01/1.02  --res_out_proof                         true
% 3.01/1.02  
% 3.01/1.02  ------ Superposition Options
% 3.01/1.02  
% 3.01/1.02  --superposition_flag                    true
% 3.01/1.02  --sup_passive_queue_type                priority_queues
% 3.01/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.02  --demod_completeness_check              fast
% 3.01/1.02  --demod_use_ground                      true
% 3.01/1.02  --sup_to_prop_solver                    passive
% 3.01/1.02  --sup_prop_simpl_new                    true
% 3.01/1.02  --sup_prop_simpl_given                  true
% 3.01/1.02  --sup_fun_splitting                     false
% 3.01/1.02  --sup_smt_interval                      50000
% 3.01/1.02  
% 3.01/1.02  ------ Superposition Simplification Setup
% 3.01/1.02  
% 3.01/1.02  --sup_indices_passive                   []
% 3.01/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.02  --sup_full_bw                           [BwDemod]
% 3.01/1.02  --sup_immed_triv                        [TrivRules]
% 3.01/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.02  --sup_immed_bw_main                     []
% 3.01/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.02  
% 3.01/1.02  ------ Combination Options
% 3.01/1.02  
% 3.01/1.02  --comb_res_mult                         3
% 3.01/1.02  --comb_sup_mult                         2
% 3.01/1.02  --comb_inst_mult                        10
% 3.01/1.02  
% 3.01/1.02  ------ Debug Options
% 3.01/1.02  
% 3.01/1.02  --dbg_backtrace                         false
% 3.01/1.02  --dbg_dump_prop_clauses                 false
% 3.01/1.02  --dbg_dump_prop_clauses_file            -
% 3.01/1.02  --dbg_out_stat                          false
% 3.01/1.02  
% 3.01/1.02  
% 3.01/1.02  
% 3.01/1.02  
% 3.01/1.02  ------ Proving...
% 3.01/1.02  
% 3.01/1.02  
% 3.01/1.02  % SZS status Theorem for theBenchmark.p
% 3.01/1.02  
% 3.01/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/1.02  
% 3.01/1.02  fof(f14,conjecture,(
% 3.01/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f15,negated_conjecture,(
% 3.01/1.02    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.01/1.02    inference(negated_conjecture,[],[f14])).
% 3.01/1.02  
% 3.01/1.02  fof(f34,plain,(
% 3.01/1.02    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.01/1.02    inference(ennf_transformation,[],[f15])).
% 3.01/1.02  
% 3.01/1.02  fof(f35,plain,(
% 3.01/1.02    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.01/1.02    inference(flattening,[],[f34])).
% 3.01/1.02  
% 3.01/1.02  fof(f40,plain,(
% 3.01/1.02    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.01/1.02    introduced(choice_axiom,[])).
% 3.01/1.02  
% 3.01/1.02  fof(f41,plain,(
% 3.01/1.02    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.01/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f40])).
% 3.01/1.02  
% 3.01/1.02  fof(f69,plain,(
% 3.01/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.01/1.02    inference(cnf_transformation,[],[f41])).
% 3.01/1.02  
% 3.01/1.02  fof(f12,axiom,(
% 3.01/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f30,plain,(
% 3.01/1.02    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.01/1.02    inference(ennf_transformation,[],[f12])).
% 3.01/1.02  
% 3.01/1.02  fof(f31,plain,(
% 3.01/1.02    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.01/1.02    inference(flattening,[],[f30])).
% 3.01/1.02  
% 3.01/1.02  fof(f63,plain,(
% 3.01/1.02    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f31])).
% 3.01/1.02  
% 3.01/1.02  fof(f67,plain,(
% 3.01/1.02    v1_funct_1(sK3)),
% 3.01/1.02    inference(cnf_transformation,[],[f41])).
% 3.01/1.02  
% 3.01/1.02  fof(f11,axiom,(
% 3.01/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f28,plain,(
% 3.01/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.01/1.02    inference(ennf_transformation,[],[f11])).
% 3.01/1.02  
% 3.01/1.02  fof(f29,plain,(
% 3.01/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.01/1.02    inference(flattening,[],[f28])).
% 3.01/1.02  
% 3.01/1.02  fof(f62,plain,(
% 3.01/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f29])).
% 3.01/1.02  
% 3.01/1.02  fof(f3,axiom,(
% 3.01/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f17,plain,(
% 3.01/1.02    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.01/1.02    inference(ennf_transformation,[],[f3])).
% 3.01/1.02  
% 3.01/1.02  fof(f38,plain,(
% 3.01/1.02    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.01/1.02    inference(nnf_transformation,[],[f17])).
% 3.01/1.02  
% 3.01/1.02  fof(f46,plain,(
% 3.01/1.02    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f38])).
% 3.01/1.02  
% 3.01/1.02  fof(f8,axiom,(
% 3.01/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f24,plain,(
% 3.01/1.02    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.02    inference(ennf_transformation,[],[f8])).
% 3.01/1.02  
% 3.01/1.02  fof(f53,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.02    inference(cnf_transformation,[],[f24])).
% 3.01/1.02  
% 3.01/1.02  fof(f7,axiom,(
% 3.01/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f23,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.02    inference(ennf_transformation,[],[f7])).
% 3.01/1.02  
% 3.01/1.02  fof(f51,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.02    inference(cnf_transformation,[],[f23])).
% 3.01/1.02  
% 3.01/1.02  fof(f70,plain,(
% 3.01/1.02    r1_tarski(sK2,sK0)),
% 3.01/1.02    inference(cnf_transformation,[],[f41])).
% 3.01/1.02  
% 3.01/1.02  fof(f10,axiom,(
% 3.01/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f26,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.02    inference(ennf_transformation,[],[f10])).
% 3.01/1.02  
% 3.01/1.02  fof(f27,plain,(
% 3.01/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.02    inference(flattening,[],[f26])).
% 3.01/1.02  
% 3.01/1.02  fof(f39,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.02    inference(nnf_transformation,[],[f27])).
% 3.01/1.02  
% 3.01/1.02  fof(f55,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.02    inference(cnf_transformation,[],[f39])).
% 3.01/1.02  
% 3.01/1.02  fof(f68,plain,(
% 3.01/1.02    v1_funct_2(sK3,sK0,sK1)),
% 3.01/1.02    inference(cnf_transformation,[],[f41])).
% 3.01/1.02  
% 3.01/1.02  fof(f9,axiom,(
% 3.01/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f25,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.02    inference(ennf_transformation,[],[f9])).
% 3.01/1.02  
% 3.01/1.02  fof(f54,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.02    inference(cnf_transformation,[],[f25])).
% 3.01/1.02  
% 3.01/1.02  fof(f6,axiom,(
% 3.01/1.02    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f21,plain,(
% 3.01/1.02    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.01/1.02    inference(ennf_transformation,[],[f6])).
% 3.01/1.02  
% 3.01/1.02  fof(f22,plain,(
% 3.01/1.02    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.01/1.02    inference(flattening,[],[f21])).
% 3.01/1.02  
% 3.01/1.02  fof(f50,plain,(
% 3.01/1.02    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f22])).
% 3.01/1.02  
% 3.01/1.02  fof(f13,axiom,(
% 3.01/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f32,plain,(
% 3.01/1.02    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.01/1.02    inference(ennf_transformation,[],[f13])).
% 3.01/1.02  
% 3.01/1.02  fof(f33,plain,(
% 3.01/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.01/1.02    inference(flattening,[],[f32])).
% 3.01/1.02  
% 3.01/1.02  fof(f66,plain,(
% 3.01/1.02    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f33])).
% 3.01/1.02  
% 3.01/1.02  fof(f61,plain,(
% 3.01/1.02    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f29])).
% 3.01/1.02  
% 3.01/1.02  fof(f65,plain,(
% 3.01/1.02    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f33])).
% 3.01/1.02  
% 3.01/1.02  fof(f72,plain,(
% 3.01/1.02    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.01/1.02    inference(cnf_transformation,[],[f41])).
% 3.01/1.02  
% 3.01/1.02  fof(f71,plain,(
% 3.01/1.02    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.01/1.02    inference(cnf_transformation,[],[f41])).
% 3.01/1.02  
% 3.01/1.02  fof(f2,axiom,(
% 3.01/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f36,plain,(
% 3.01/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.01/1.02    inference(nnf_transformation,[],[f2])).
% 3.01/1.02  
% 3.01/1.02  fof(f37,plain,(
% 3.01/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.01/1.02    inference(flattening,[],[f36])).
% 3.01/1.02  
% 3.01/1.02  fof(f44,plain,(
% 3.01/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.01/1.02    inference(cnf_transformation,[],[f37])).
% 3.01/1.02  
% 3.01/1.02  fof(f74,plain,(
% 3.01/1.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.01/1.02    inference(equality_resolution,[],[f44])).
% 3.01/1.02  
% 3.01/1.02  fof(f45,plain,(
% 3.01/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.01/1.02    inference(cnf_transformation,[],[f37])).
% 3.01/1.02  
% 3.01/1.02  fof(f73,plain,(
% 3.01/1.02    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.01/1.02    inference(equality_resolution,[],[f45])).
% 3.01/1.02  
% 3.01/1.02  fof(f56,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.02    inference(cnf_transformation,[],[f39])).
% 3.01/1.02  
% 3.01/1.02  fof(f79,plain,(
% 3.01/1.02    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.01/1.02    inference(equality_resolution,[],[f56])).
% 3.01/1.02  
% 3.01/1.02  fof(f59,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.02    inference(cnf_transformation,[],[f39])).
% 3.01/1.02  
% 3.01/1.02  fof(f77,plain,(
% 3.01/1.02    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.01/1.02    inference(equality_resolution,[],[f59])).
% 3.01/1.02  
% 3.01/1.02  fof(f43,plain,(
% 3.01/1.02    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f37])).
% 3.01/1.02  
% 3.01/1.02  cnf(c_28,negated_conjecture,
% 3.01/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.01/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1803,plain,
% 3.01/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_21,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.01/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1806,plain,
% 3.01/1.02      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.01/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.01/1.02      | v1_funct_1(X2) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3887,plain,
% 3.01/1.02      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.01/1.02      | v1_funct_1(sK3) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1803,c_1806]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_30,negated_conjecture,
% 3.01/1.02      ( v1_funct_1(sK3) ),
% 3.01/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2106,plain,
% 3.01/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.01/1.02      | ~ v1_funct_1(sK3)
% 3.01/1.02      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_21]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2259,plain,
% 3.01/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.01/1.02      | ~ v1_funct_1(sK3)
% 3.01/1.02      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_2106]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3995,plain,
% 3.01/1.02      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_3887,c_30,c_28,c_2259]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_19,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | ~ v1_funct_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1808,plain,
% 3.01/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.01/1.02      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.01/1.02      | v1_funct_1(X0) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_5081,plain,
% 3.01/1.02      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.01/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.01/1.02      | v1_funct_1(sK3) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_3995,c_1808]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_31,plain,
% 3.01/1.02      ( v1_funct_1(sK3) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_33,plain,
% 3.01/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_5657,plain,
% 3.01/1.02      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_5081,c_31,c_33]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_5,plain,
% 3.01/1.02      ( ~ v5_relat_1(X0,X1)
% 3.01/1.02      | r1_tarski(k2_relat_1(X0),X1)
% 3.01/1.02      | ~ v1_relat_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_10,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | v5_relat_1(X0,X2) ),
% 3.01/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_326,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | r1_tarski(k2_relat_1(X3),X4)
% 3.01/1.02      | ~ v1_relat_1(X3)
% 3.01/1.02      | X0 != X3
% 3.01/1.02      | X2 != X4 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_10]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_327,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | r1_tarski(k2_relat_1(X0),X2)
% 3.01/1.02      | ~ v1_relat_1(X0) ),
% 3.01/1.02      inference(unflattening,[status(thm)],[c_326]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_9,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | v1_relat_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_331,plain,
% 3.01/1.02      ( r1_tarski(k2_relat_1(X0),X2)
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_327,c_9]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_332,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.01/1.02      inference(renaming,[status(thm)],[c_331]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1800,plain,
% 3.01/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.01/1.02      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_5667,plain,
% 3.01/1.02      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_5657,c_1800]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_27,negated_conjecture,
% 3.01/1.02      ( r1_tarski(sK2,sK0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1804,plain,
% 3.01/1.02      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_18,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.01/1.02      | k1_xboole_0 = X2 ),
% 3.01/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_29,negated_conjecture,
% 3.01/1.02      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.01/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_683,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.01/1.02      | sK3 != X0
% 3.01/1.02      | sK1 != X2
% 3.01/1.02      | sK0 != X1
% 3.01/1.02      | k1_xboole_0 = X2 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_684,plain,
% 3.01/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.01/1.02      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.01/1.02      | k1_xboole_0 = sK1 ),
% 3.01/1.02      inference(unflattening,[status(thm)],[c_683]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_686,plain,
% 3.01/1.02      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_684,c_28]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_12,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1809,plain,
% 3.01/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.01/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2726,plain,
% 3.01/1.02      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1803,c_1809]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2916,plain,
% 3.01/1.02      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_686,c_2726]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_8,plain,
% 3.01/1.02      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.01/1.02      | ~ v1_relat_1(X1)
% 3.01/1.02      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.01/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1811,plain,
% 3.01/1.02      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.01/1.02      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.01/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2975,plain,
% 3.01/1.02      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.01/1.02      | sK1 = k1_xboole_0
% 3.01/1.02      | r1_tarski(X0,sK0) != iProver_top
% 3.01/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_2916,c_1811]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2043,plain,
% 3.01/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.01/1.02      | v1_relat_1(sK3) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2044,plain,
% 3.01/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.01/1.02      | v1_relat_1(sK3) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_2043]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2980,plain,
% 3.01/1.02      ( r1_tarski(X0,sK0) != iProver_top
% 3.01/1.02      | sK1 = k1_xboole_0
% 3.01/1.02      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_2975,c_33,c_2044]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2981,plain,
% 3.01/1.02      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.01/1.02      | sK1 = k1_xboole_0
% 3.01/1.02      | r1_tarski(X0,sK0) != iProver_top ),
% 3.01/1.02      inference(renaming,[status(thm)],[c_2980]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2989,plain,
% 3.01/1.02      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1804,c_2981]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_22,plain,
% 3.01/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.01/1.02      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | ~ v1_relat_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1805,plain,
% 3.01/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.01/1.02      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.01/1.02      | v1_funct_1(X0) != iProver_top
% 3.01/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4122,plain,
% 3.01/1.02      ( sK1 = k1_xboole_0
% 3.01/1.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.01/1.02      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.01/1.02      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.01/1.02      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_2989,c_1805]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_20,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.01/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1807,plain,
% 3.01/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.01/1.02      | v1_funct_1(X0) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3237,plain,
% 3.01/1.02      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.01/1.02      | v1_funct_1(sK3) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1803,c_1807]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2086,plain,
% 3.01/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.01/1.02      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.01/1.02      | ~ v1_funct_1(sK3) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_20]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2251,plain,
% 3.01/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.01/1.02      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.01/1.02      | ~ v1_funct_1(sK3) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_2086]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2252,plain,
% 3.01/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.01/1.02      | v1_funct_1(sK3) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_2251]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3670,plain,
% 3.01/1.02      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_3237,c_31,c_33,c_2252]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4004,plain,
% 3.01/1.02      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_3995,c_3670]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4641,plain,
% 3.01/1.02      ( sK1 = k1_xboole_0
% 3.01/1.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.01/1.02      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.01/1.02      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.01/1.02      inference(forward_subsumption_resolution,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_4122,c_4004]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_23,plain,
% 3.01/1.02      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.01/1.02      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | ~ v1_relat_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_25,negated_conjecture,
% 3.01/1.02      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.01/1.02      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.01/1.02      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.01/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_694,plain,
% 3.01/1.02      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.01/1.02      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.01/1.02      | ~ v1_relat_1(X0)
% 3.01/1.02      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.01/1.02      | k1_relat_1(X0) != sK2
% 3.01/1.02      | sK1 != X1 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_23,c_25]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_695,plain,
% 3.01/1.02      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.01/1.02      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 3.01/1.02      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.01/1.02      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.01/1.02      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.01/1.02      inference(unflattening,[status(thm)],[c_694]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_707,plain,
% 3.01/1.02      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.01/1.02      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.01/1.02      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.01/1.02      inference(forward_subsumption_resolution,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_695,c_9,c_332]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1791,plain,
% 3.01/1.02      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.01/1.02      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_707]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4002,plain,
% 3.01/1.02      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.01/1.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.01/1.02      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_3995,c_1791]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4018,plain,
% 3.01/1.02      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.01/1.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.01/1.02      inference(forward_subsumption_resolution,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_4002,c_4004]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4712,plain,
% 3.01/1.02      ( sK1 = k1_xboole_0
% 3.01/1.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_2989,c_4018]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4848,plain,
% 3.01/1.02      ( sK1 = k1_xboole_0
% 3.01/1.02      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 3.01/1.02      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_4641,c_4712]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_5756,plain,
% 3.01/1.02      ( sK1 = k1_xboole_0
% 3.01/1.02      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_5667,c_4848]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1810,plain,
% 3.01/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.01/1.02      | v1_relat_1(X0) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_5670,plain,
% 3.01/1.02      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_5657,c_1810]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6647,plain,
% 3.01/1.02      ( sK1 = k1_xboole_0 ),
% 3.01/1.02      inference(forward_subsumption_resolution,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_5756,c_5670]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6655,plain,
% 3.01/1.02      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_6647,c_5657]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_26,negated_conjecture,
% 3.01/1.02      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.01/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6670,plain,
% 3.01/1.02      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_6647,c_26]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6671,plain,
% 3.01/1.02      ( sK0 = k1_xboole_0 ),
% 3.01/1.02      inference(equality_resolution_simp,[status(thm)],[c_6670]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6704,plain,
% 3.01/1.02      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_6655,c_6671]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2,plain,
% 3.01/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.01/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6706,plain,
% 3.01/1.02      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_6704,c_2]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6657,plain,
% 3.01/1.02      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.01/1.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_6647,c_4018]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1,plain,
% 3.01/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.01/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6696,plain,
% 3.01/1.02      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.01/1.02      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_6657,c_1]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6708,plain,
% 3.01/1.02      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2 ),
% 3.01/1.02      inference(backward_subsumption_resolution,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_6706,c_6696]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6665,plain,
% 3.01/1.02      ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_6647,c_2726]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_17,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.01/1.02      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.01/1.02      inference(cnf_transformation,[],[f79]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_627,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.01/1.02      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.01/1.02      | sK3 != X0
% 3.01/1.02      | sK1 != X1
% 3.01/1.02      | sK0 != k1_xboole_0 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_628,plain,
% 3.01/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.01/1.02      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.01/1.02      | sK0 != k1_xboole_0 ),
% 3.01/1.02      inference(unflattening,[status(thm)],[c_627]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1794,plain,
% 3.01/1.02      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.01/1.02      | sK0 != k1_xboole_0
% 3.01/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_628]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1868,plain,
% 3.01/1.02      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.01/1.02      | sK0 != k1_xboole_0
% 3.01/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_1794,c_2]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6667,plain,
% 3.01/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 3.01/1.02      | sK0 != k1_xboole_0
% 3.01/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_6647,c_1868]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6678,plain,
% 3.01/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 3.01/1.02      | k1_xboole_0 != k1_xboole_0
% 3.01/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_6667,c_6671]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6679,plain,
% 3.01/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 3.01/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.01/1.02      inference(equality_resolution_simp,[status(thm)],[c_6678]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6669,plain,
% 3.01/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_6647,c_1803]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6674,plain,
% 3.01/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_6669,c_6671]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6676,plain,
% 3.01/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_6674,c_2]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6682,plain,
% 3.01/1.02      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 3.01/1.02      inference(forward_subsumption_resolution,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_6679,c_6676]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6685,plain,
% 3.01/1.02      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_6665,c_6671,c_6682]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1369,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2407,plain,
% 3.01/1.02      ( X0 != X1 | X0 = sK0 | sK0 != X1 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_1369]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3447,plain,
% 3.01/1.02      ( k1_relat_1(sK3) != X0 | k1_relat_1(sK3) = sK0 | sK0 != X0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_2407]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3448,plain,
% 3.01/1.02      ( k1_relat_1(sK3) = sK0
% 3.01/1.02      | k1_relat_1(sK3) != k1_xboole_0
% 3.01/1.02      | sK0 != k1_xboole_0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_3447]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2119,plain,
% 3.01/1.02      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 3.01/1.02      | ~ v1_relat_1(sK3)
% 3.01/1.02      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2813,plain,
% 3.01/1.02      ( ~ r1_tarski(sK2,k1_relat_1(sK3))
% 3.01/1.02      | ~ v1_relat_1(sK3)
% 3.01/1.02      | k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_2119]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1370,plain,
% 3.01/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.01/1.02      theory(equality) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2091,plain,
% 3.01/1.02      ( r1_tarski(X0,X1) | ~ r1_tarski(sK2,sK0) | X0 != sK2 | X1 != sK0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_1370]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2192,plain,
% 3.01/1.02      ( r1_tarski(sK2,X0)
% 3.01/1.02      | ~ r1_tarski(sK2,sK0)
% 3.01/1.02      | X0 != sK0
% 3.01/1.02      | sK2 != sK2 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_2091]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2812,plain,
% 3.01/1.02      ( r1_tarski(sK2,k1_relat_1(sK3))
% 3.01/1.02      | ~ r1_tarski(sK2,sK0)
% 3.01/1.02      | k1_relat_1(sK3) != sK0
% 3.01/1.02      | sK2 != sK2 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_2192]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_14,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.01/1.02      | k1_xboole_0 = X1
% 3.01/1.02      | k1_xboole_0 = X0 ),
% 3.01/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_563,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.01/1.02      | sK3 != X0
% 3.01/1.02      | sK1 != k1_xboole_0
% 3.01/1.02      | sK0 != X1
% 3.01/1.02      | k1_xboole_0 = X0
% 3.01/1.02      | k1_xboole_0 = X1 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_564,plain,
% 3.01/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 3.01/1.02      | sK1 != k1_xboole_0
% 3.01/1.02      | k1_xboole_0 = sK3
% 3.01/1.02      | k1_xboole_0 = sK0 ),
% 3.01/1.02      inference(unflattening,[status(thm)],[c_563]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1797,plain,
% 3.01/1.02      ( sK1 != k1_xboole_0
% 3.01/1.02      | k1_xboole_0 = sK3
% 3.01/1.02      | k1_xboole_0 = sK0
% 3.01/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_564]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1875,plain,
% 3.01/1.02      ( sK3 = k1_xboole_0
% 3.01/1.02      | sK1 != k1_xboole_0
% 3.01/1.02      | sK0 = k1_xboole_0
% 3.01/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_1797,c_1]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3,plain,
% 3.01/1.02      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.01/1.02      | k1_xboole_0 = X0
% 3.01/1.02      | k1_xboole_0 = X1 ),
% 3.01/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_97,plain,
% 3.01/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.01/1.02      | k1_xboole_0 = k1_xboole_0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_98,plain,
% 3.01/1.02      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2058,plain,
% 3.01/1.02      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_1369]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2331,plain,
% 3.01/1.02      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_2058]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1368,plain,( X0 = X0 ),theory(equality) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2332,plain,
% 3.01/1.02      ( sK0 = sK0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_1368]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2423,plain,
% 3.01/1.02      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_1369]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2424,plain,
% 3.01/1.02      ( sK1 != k1_xboole_0
% 3.01/1.02      | k1_xboole_0 = sK1
% 3.01/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_2423]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2437,plain,
% 3.01/1.02      ( sK0 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_1875,c_26,c_97,c_98,c_2331,c_2332,c_2424]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2438,plain,
% 3.01/1.02      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 3.01/1.02      inference(renaming,[status(thm)],[c_2437]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2193,plain,
% 3.01/1.02      ( sK2 = sK2 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_1368]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(contradiction,plain,
% 3.01/1.02      ( $false ),
% 3.01/1.02      inference(minisat,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_6708,c_6685,c_6647,c_3448,c_2813,c_2812,c_2438,c_2193,
% 3.01/1.02                 c_2043,c_27,c_28]) ).
% 3.01/1.02  
% 3.01/1.02  
% 3.01/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/1.02  
% 3.01/1.02  ------                               Statistics
% 3.01/1.02  
% 3.01/1.02  ------ General
% 3.01/1.02  
% 3.01/1.02  abstr_ref_over_cycles:                  0
% 3.01/1.02  abstr_ref_under_cycles:                 0
% 3.01/1.02  gc_basic_clause_elim:                   0
% 3.01/1.02  forced_gc_time:                         0
% 3.01/1.02  parsing_time:                           0.008
% 3.01/1.02  unif_index_cands_time:                  0.
% 3.01/1.02  unif_index_add_time:                    0.
% 3.01/1.02  orderings_time:                         0.
% 3.01/1.02  out_proof_time:                         0.013
% 3.01/1.02  total_time:                             0.183
% 3.01/1.02  num_of_symbols:                         50
% 3.01/1.02  num_of_terms:                           5396
% 3.01/1.02  
% 3.01/1.02  ------ Preprocessing
% 3.01/1.02  
% 3.01/1.02  num_of_splits:                          0
% 3.01/1.02  num_of_split_atoms:                     0
% 3.01/1.02  num_of_reused_defs:                     0
% 3.01/1.02  num_eq_ax_congr_red:                    15
% 3.01/1.02  num_of_sem_filtered_clauses:            1
% 3.01/1.02  num_of_subtypes:                        0
% 3.01/1.02  monotx_restored_types:                  0
% 3.01/1.02  sat_num_of_epr_types:                   0
% 3.01/1.02  sat_num_of_non_cyclic_types:            0
% 3.01/1.02  sat_guarded_non_collapsed_types:        0
% 3.01/1.02  num_pure_diseq_elim:                    0
% 3.01/1.02  simp_replaced_by:                       0
% 3.01/1.02  res_preprocessed:                       140
% 3.01/1.02  prep_upred:                             0
% 3.01/1.02  prep_unflattend:                        77
% 3.01/1.02  smt_new_axioms:                         0
% 3.01/1.02  pred_elim_cands:                        4
% 3.01/1.02  pred_elim:                              3
% 3.01/1.02  pred_elim_cl:                           1
% 3.01/1.02  pred_elim_cycles:                       6
% 3.01/1.02  merged_defs:                            0
% 3.01/1.02  merged_defs_ncl:                        0
% 3.01/1.02  bin_hyper_res:                          0
% 3.01/1.02  prep_cycles:                            4
% 3.01/1.02  pred_elim_time:                         0.013
% 3.01/1.02  splitting_time:                         0.
% 3.01/1.02  sem_filter_time:                        0.
% 3.01/1.02  monotx_time:                            0.
% 3.01/1.02  subtype_inf_time:                       0.
% 3.01/1.02  
% 3.01/1.02  ------ Problem properties
% 3.01/1.02  
% 3.01/1.02  clauses:                                29
% 3.01/1.02  conjectures:                            4
% 3.01/1.02  epr:                                    4
% 3.01/1.02  horn:                                   24
% 3.01/1.02  ground:                                 12
% 3.01/1.02  unary:                                  5
% 3.01/1.02  binary:                                 8
% 3.01/1.02  lits:                                   83
% 3.01/1.02  lits_eq:                                35
% 3.01/1.02  fd_pure:                                0
% 3.01/1.02  fd_pseudo:                              0
% 3.01/1.02  fd_cond:                                4
% 3.01/1.02  fd_pseudo_cond:                         0
% 3.01/1.02  ac_symbols:                             0
% 3.01/1.02  
% 3.01/1.02  ------ Propositional Solver
% 3.01/1.02  
% 3.01/1.02  prop_solver_calls:                      27
% 3.01/1.02  prop_fast_solver_calls:                 1249
% 3.01/1.02  smt_solver_calls:                       0
% 3.01/1.02  smt_fast_solver_calls:                  0
% 3.01/1.02  prop_num_of_clauses:                    2330
% 3.01/1.02  prop_preprocess_simplified:             7205
% 3.01/1.02  prop_fo_subsumed:                       29
% 3.01/1.02  prop_solver_time:                       0.
% 3.01/1.02  smt_solver_time:                        0.
% 3.01/1.02  smt_fast_solver_time:                   0.
% 3.01/1.02  prop_fast_solver_time:                  0.
% 3.01/1.02  prop_unsat_core_time:                   0.
% 3.01/1.02  
% 3.01/1.02  ------ QBF
% 3.01/1.02  
% 3.01/1.02  qbf_q_res:                              0
% 3.01/1.02  qbf_num_tautologies:                    0
% 3.01/1.02  qbf_prep_cycles:                        0
% 3.01/1.02  
% 3.01/1.02  ------ BMC1
% 3.01/1.02  
% 3.01/1.02  bmc1_current_bound:                     -1
% 3.01/1.02  bmc1_last_solved_bound:                 -1
% 3.01/1.02  bmc1_unsat_core_size:                   -1
% 3.01/1.02  bmc1_unsat_core_parents_size:           -1
% 3.01/1.02  bmc1_merge_next_fun:                    0
% 3.01/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.01/1.02  
% 3.01/1.02  ------ Instantiation
% 3.01/1.02  
% 3.01/1.02  inst_num_of_clauses:                    744
% 3.01/1.02  inst_num_in_passive:                    318
% 3.01/1.02  inst_num_in_active:                     366
% 3.01/1.02  inst_num_in_unprocessed:                60
% 3.01/1.02  inst_num_of_loops:                      410
% 3.01/1.02  inst_num_of_learning_restarts:          0
% 3.01/1.02  inst_num_moves_active_passive:          42
% 3.01/1.02  inst_lit_activity:                      0
% 3.01/1.02  inst_lit_activity_moves:                0
% 3.01/1.02  inst_num_tautologies:                   0
% 3.01/1.02  inst_num_prop_implied:                  0
% 3.01/1.02  inst_num_existing_simplified:           0
% 3.01/1.02  inst_num_eq_res_simplified:             0
% 3.01/1.02  inst_num_child_elim:                    0
% 3.01/1.02  inst_num_of_dismatching_blockings:      98
% 3.01/1.02  inst_num_of_non_proper_insts:           517
% 3.01/1.02  inst_num_of_duplicates:                 0
% 3.01/1.02  inst_inst_num_from_inst_to_res:         0
% 3.01/1.02  inst_dismatching_checking_time:         0.
% 3.01/1.02  
% 3.01/1.02  ------ Resolution
% 3.01/1.02  
% 3.01/1.02  res_num_of_clauses:                     0
% 3.01/1.02  res_num_in_passive:                     0
% 3.01/1.02  res_num_in_active:                      0
% 3.01/1.02  res_num_of_loops:                       144
% 3.01/1.02  res_forward_subset_subsumed:            13
% 3.01/1.02  res_backward_subset_subsumed:           0
% 3.01/1.02  res_forward_subsumed:                   0
% 3.01/1.02  res_backward_subsumed:                  0
% 3.01/1.02  res_forward_subsumption_resolution:     5
% 3.01/1.02  res_backward_subsumption_resolution:    0
% 3.01/1.02  res_clause_to_clause_subsumption:       306
% 3.01/1.02  res_orphan_elimination:                 0
% 3.01/1.02  res_tautology_del:                      59
% 3.01/1.02  res_num_eq_res_simplified:              1
% 3.01/1.02  res_num_sel_changes:                    0
% 3.01/1.02  res_moves_from_active_to_pass:          0
% 3.01/1.02  
% 3.01/1.02  ------ Superposition
% 3.01/1.02  
% 3.01/1.02  sup_time_total:                         0.
% 3.01/1.02  sup_time_generating:                    0.
% 3.01/1.02  sup_time_sim_full:                      0.
% 3.01/1.02  sup_time_sim_immed:                     0.
% 3.01/1.02  
% 3.01/1.02  sup_num_of_clauses:                     82
% 3.01/1.02  sup_num_in_active:                      42
% 3.01/1.02  sup_num_in_passive:                     40
% 3.01/1.02  sup_num_of_loops:                       81
% 3.01/1.02  sup_fw_superposition:                   58
% 3.01/1.02  sup_bw_superposition:                   53
% 3.01/1.02  sup_immediate_simplified:               38
% 3.01/1.02  sup_given_eliminated:                   0
% 3.01/1.02  comparisons_done:                       0
% 3.01/1.02  comparisons_avoided:                    22
% 3.01/1.02  
% 3.01/1.02  ------ Simplifications
% 3.01/1.02  
% 3.01/1.02  
% 3.01/1.02  sim_fw_subset_subsumed:                 10
% 3.01/1.02  sim_bw_subset_subsumed:                 11
% 3.01/1.02  sim_fw_subsumed:                        2
% 3.01/1.02  sim_bw_subsumed:                        1
% 3.01/1.02  sim_fw_subsumption_res:                 10
% 3.01/1.02  sim_bw_subsumption_res:                 2
% 3.01/1.02  sim_tautology_del:                      5
% 3.01/1.02  sim_eq_tautology_del:                   11
% 3.01/1.02  sim_eq_res_simp:                        3
% 3.01/1.02  sim_fw_demodulated:                     13
% 3.01/1.02  sim_bw_demodulated:                     30
% 3.01/1.02  sim_light_normalised:                   13
% 3.01/1.02  sim_joinable_taut:                      0
% 3.01/1.02  sim_joinable_simp:                      0
% 3.01/1.02  sim_ac_normalised:                      0
% 3.01/1.02  sim_smt_subsumption:                    0
% 3.01/1.02  
%------------------------------------------------------------------------------
