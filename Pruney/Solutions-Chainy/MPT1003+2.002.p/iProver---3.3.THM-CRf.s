%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:24 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 7.62s
% Verified   : 
% Statistics : Number of formulae       :  265 (293222 expanded)
%              Number of clauses        :  194 (110727 expanded)
%              Number of leaves         :   20 (52845 expanded)
%              Depth                    :   43
%              Number of atoms          :  735 (1248934 expanded)
%              Number of equality atoms :  462 (596407 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) != sK0
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) != sK0
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f43])).

fof(f75,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f77,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f64])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_729,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_730,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_732,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_730,c_31])).

cnf(c_1966,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1971,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3648,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1966,c_1971])).

cnf(c_3750,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_732,c_3648])).

cnf(c_26,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_481,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_33])).

cnf(c_482,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
    | ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_1964,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_482])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_483,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_482])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2232,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2233,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2232])).

cnf(c_2291,plain,
    ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1964,c_36,c_483,c_2233])).

cnf(c_2292,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2291])).

cnf(c_3829,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3750,c_2292])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1978,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_27,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_466,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_33])).

cnf(c_467,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
    | ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_740,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(sK2),X3)
    | ~ v1_relat_1(sK2)
    | X3 != X2
    | k1_relset_1(X1,X2,X0) = X1
    | k1_relat_1(sK2) != X1
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_467])).

cnf(c_741,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
    | ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k1_relset_1(k1_relat_1(sK2),X0,sK2) = k1_relat_1(sK2)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_740])).

cnf(c_745,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k1_relset_1(k1_relat_1(sK2),X0,sK2) = k1_relat_1(sK2)
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_741,c_482])).

cnf(c_1958,plain,
    ( k1_relset_1(k1_relat_1(sK2),X0,sK2) = k1_relat_1(sK2)
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_742,plain,
    ( k1_relset_1(k1_relat_1(sK2),X0,sK2) = k1_relat_1(sK2)
    | k1_xboole_0 = X0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) != iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_2669,plain,
    ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | k1_xboole_0 = X0
    | k1_relset_1(k1_relat_1(sK2),X0,sK2) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1958,c_36,c_483,c_742,c_2233])).

cnf(c_2670,plain,
    ( k1_relset_1(k1_relat_1(sK2),X0,sK2) = k1_relat_1(sK2)
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2669])).

cnf(c_2676,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1978,c_2670])).

cnf(c_3826,plain,
    ( k1_relset_1(sK0,k2_relat_1(sK2),sK2) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3750,c_2676])).

cnf(c_21,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_496,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = X1
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_497,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k8_relset_1(X0,X1,sK2,X1) = X0
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_764,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | X3 != X1
    | X4 != X2
    | k8_relset_1(X3,X4,sK2,X4) = X3
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X4 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_497])).

cnf(c_765,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k8_relset_1(X0,X1,sK2,X1) = X0
    | k1_relset_1(X0,X1,sK2) != X0
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_764])).

cnf(c_1957,plain,
    ( k8_relset_1(X0,X1,sK2,X1) = X0
    | k1_relset_1(X0,X1,sK2) != X0
    | k1_xboole_0 = X1
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_765])).

cnf(c_4025,plain,
    ( k8_relset_1(sK0,k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = sK0
    | k1_relat_1(sK2) != sK0
    | k2_relat_1(sK2) = k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3826,c_1957])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_101,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_102,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2371,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_relat_1(sK2)))
    | r1_tarski(X0,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2373,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_relat_1(sK2)))
    | r1_tarski(k1_xboole_0,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_2371])).

cnf(c_1337,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2587,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1337])).

cnf(c_2588,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2587])).

cnf(c_2344,plain,
    ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0))
    | r1_tarski(k2_relat_1(sK2),X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2886,plain,
    ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_2344])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3233,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),X0)
    | k2_relat_1(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3235,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3233])).

cnf(c_1336,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3239,plain,
    ( k2_relat_1(sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1336])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_451,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_33])).

cnf(c_452,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_1965,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k2_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_453,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k2_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_2238,plain,
    ( r1_tarski(X0,k2_relat_1(sK2)) != iProver_top
    | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1965,c_36,c_453,c_2233])).

cnf(c_2239,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k2_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2238])).

cnf(c_2429,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2))) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1978,c_2239])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1970,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4802,plain,
    ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1966,c_1970])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1972,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4945,plain,
    ( m1_subset_1(k9_relat_1(sK2,X0),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4802,c_1972])).

cnf(c_5202,plain,
    ( m1_subset_1(k9_relat_1(sK2,X0),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4945,c_36])).

cnf(c_5210,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2429,c_5202])).

cnf(c_5217,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5210])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_5540,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_relat_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1338,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2355,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK2),X2)
    | X2 != X1
    | k2_relat_1(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_1338])).

cnf(c_3238,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),X0)
    | r1_tarski(k2_relat_1(sK2),X1)
    | X1 != X0
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2355])).

cnf(c_8293,plain,
    ( r1_tarski(k2_relat_1(sK2),X0)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | X0 != sK1
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3238])).

cnf(c_8299,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | k2_relat_1(sK2) != k2_relat_1(sK2)
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_8293])).

cnf(c_10312,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k8_relset_1(sK0,k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = sK0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4025,c_101,c_102,c_2373,c_2588,c_2886,c_3235,c_3239,c_3750,c_5217,c_5540,c_8299])).

cnf(c_10313,plain,
    ( k8_relset_1(sK0,k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = sK0
    | k2_relat_1(sK2) = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10312])).

cnf(c_10320,plain,
    ( k8_relset_1(sK0,k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = sK0
    | k2_relat_1(sK2) = k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3829,c_10313])).

cnf(c_2350,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_10336,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
    | k8_relset_1(sK0,k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = sK0
    | k2_relat_1(sK2) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10320])).

cnf(c_10338,plain,
    ( k8_relset_1(sK0,k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = sK0
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10320,c_101,c_102,c_2350,c_2373,c_2588,c_2886,c_3235,c_3239,c_5217,c_5540,c_8299,c_10336])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1969,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4270,plain,
    ( k8_relset_1(k1_relat_1(sK2),X0,sK2,X1) = k10_relat_1(sK2,X1)
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2292,c_1969])).

cnf(c_4443,plain,
    ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1978,c_4270])).

cnf(c_6221,plain,
    ( k8_relset_1(sK0,k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3750,c_4443])).

cnf(c_10345,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = sK0
    | k2_relat_1(sK2) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10338,c_6221])).

cnf(c_10470,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k10_relat_1(sK2,k2_relat_1(sK2)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10345,c_101,c_102,c_2373,c_2588,c_2886,c_3235,c_3239,c_5217,c_5540,c_8299])).

cnf(c_10471,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = sK0
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_10470])).

cnf(c_10474,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10471,c_2429])).

cnf(c_4269,plain,
    ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1966,c_1969])).

cnf(c_29,negated_conjecture,
    ( k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_4359,plain,
    ( k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,sK0)) != sK0 ),
    inference(demodulation,[status(thm)],[c_4269,c_29])).

cnf(c_4944,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) != sK0 ),
    inference(demodulation,[status(thm)],[c_4802,c_4359])).

cnf(c_10482,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) != sK0
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10474,c_4944])).

cnf(c_10617,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10482,c_10471])).

cnf(c_10678,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10617,c_2292])).

cnf(c_98,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2345,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2344])).

cnf(c_2464,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_1336])).

cnf(c_1341,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2273,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1341])).

cnf(c_2463,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | X0 != k1_xboole_0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2273])).

cnf(c_3121,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | k2_relat_1(sK2) != k1_xboole_0
    | k1_zfmisc_1(X0) != k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_2463])).

cnf(c_3127,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | k1_zfmisc_1(X0) != k1_zfmisc_1(X0)
    | m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3121])).

cnf(c_11184,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10678,c_36,c_98,c_483,c_2233,c_2345,c_2464,c_3127,c_10471,c_10482])).

cnf(c_11192,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3750,c_11184])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1968,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11242,plain,
    ( k8_relset_1(sK0,X0,sK2,X0) = k1_relset_1(sK0,X0,sK2)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11192,c_1968])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1974,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2970,plain,
    ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2292,c_1974])).

cnf(c_1979,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4236,plain,
    ( k2_zfmisc_1(k1_relat_1(sK2),X0) = sK2
    | r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),X0),sK2) != iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2970,c_1979])).

cnf(c_8324,plain,
    ( k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0) = sK2
    | r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_4236])).

cnf(c_8337,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8324,c_4])).

cnf(c_3994,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3995,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3994])).

cnf(c_3997,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3995])).

cnf(c_6732,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6735,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6732])).

cnf(c_8757,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8337,c_3997,c_6735])).

cnf(c_8758,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8757])).

cnf(c_10639,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10617,c_8758])).

cnf(c_93,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_99,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2357,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k2_relat_1(sK2) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2355])).

cnf(c_3996,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_3994])).

cnf(c_8344,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8337])).

cnf(c_12372,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10639,c_93,c_99,c_101,c_102,c_2357,c_3996,c_6732,c_8344,c_10471,c_10482])).

cnf(c_17048,plain,
    ( k8_relset_1(sK0,X0,k1_xboole_0,X0) = k1_relset_1(sK0,X0,k1_xboole_0)
    | sK1 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11242,c_12372])).

cnf(c_12409,plain,
    ( k1_relset_1(sK0,sK1,k1_xboole_0) = sK0
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12372,c_732])).

cnf(c_1976,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3645,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1976,c_1971])).

cnf(c_12414,plain,
    ( k1_relat_1(k1_xboole_0) = sK0
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12409,c_3645])).

cnf(c_100,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_620,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK2 != X0
    | sK1 != k1_xboole_0
    | sK0 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_32])).

cnf(c_621,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_1963,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_621])).

cnf(c_2084,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1963,c_4])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2257,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1337])).

cnf(c_2394,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2257])).

cnf(c_2395,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1336])).

cnf(c_2590,plain,
    ( sK0 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2084,c_30,c_101,c_102,c_2394,c_2395,c_2588])).

cnf(c_2591,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2590])).

cnf(c_3341,plain,
    ( X0 != X1
    | X0 = sK0
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_1337])).

cnf(c_7100,plain,
    ( k1_relat_1(X0) != X1
    | k1_relat_1(X0) = sK0
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_3341])).

cnf(c_7106,plain,
    ( k1_relat_1(k1_xboole_0) = sK0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7100])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK2 != X0
    | sK1 != X1
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_661,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_660])).

cnf(c_1961,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_2056,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1961,c_5])).

cnf(c_12407,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12372,c_2056])).

cnf(c_12424,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12407,c_3645])).

cnf(c_13399,plain,
    ( k1_relat_1(k1_xboole_0) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12414,c_100,c_2591,c_7106,c_12424])).

cnf(c_13402,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = sK0 ),
    inference(demodulation,[status(thm)],[c_13399,c_3645])).

cnf(c_11197,plain,
    ( k8_relset_1(k1_relat_1(sK2),X0,sK2,X1) = k10_relat_1(sK2,X1) ),
    inference(superposition,[status(thm)],[c_11184,c_1969])).

cnf(c_14946,plain,
    ( k8_relset_1(sK0,X0,k1_xboole_0,X1) = k10_relat_1(k1_xboole_0,X1) ),
    inference(light_normalisation,[status(thm)],[c_11197,c_12372,c_13399])).

cnf(c_17049,plain,
    ( k10_relat_1(k1_xboole_0,X0) = sK0
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_17048,c_13402,c_14946])).

cnf(c_12394,plain,
    ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,sK0)) != sK0 ),
    inference(demodulation,[status(thm)],[c_12372,c_4944])).

cnf(c_17054,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17049,c_12394])).

cnf(c_6609,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) = k1_relset_1(sK0,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1966,c_1968])).

cnf(c_6633,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_6609,c_3648])).

cnf(c_6849,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_6633,c_4269])).

cnf(c_12388,plain,
    ( k10_relat_1(k1_xboole_0,sK1) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_12372,c_6849])).

cnf(c_13497,plain,
    ( k10_relat_1(k1_xboole_0,sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_12388,c_13399])).

cnf(c_17173,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = sK0 ),
    inference(demodulation,[status(thm)],[c_17054,c_13497])).

cnf(c_17176,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_17054,c_2591])).

cnf(c_17178,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_17176])).

cnf(c_17181,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_17173,c_17178])).

cnf(c_2967,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1976,c_1974])).

cnf(c_4688,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2967,c_2239])).

cnf(c_12393,plain,
    ( k9_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12372,c_4688])).

cnf(c_26375,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_17181,c_12393])).

cnf(c_17792,plain,
    ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_17178,c_12394])).

cnf(c_26379,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_26375,c_17792])).

cnf(c_26381,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_26379,c_17181])).

cnf(c_26382,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_26381])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:55:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.62/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.62/1.49  
% 7.62/1.49  ------  iProver source info
% 7.62/1.49  
% 7.62/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.62/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.62/1.49  git: non_committed_changes: false
% 7.62/1.49  git: last_make_outside_of_git: false
% 7.62/1.49  
% 7.62/1.49  ------ 
% 7.62/1.49  
% 7.62/1.49  ------ Input Options
% 7.62/1.49  
% 7.62/1.49  --out_options                           all
% 7.62/1.49  --tptp_safe_out                         true
% 7.62/1.49  --problem_path                          ""
% 7.62/1.49  --include_path                          ""
% 7.62/1.49  --clausifier                            res/vclausify_rel
% 7.62/1.49  --clausifier_options                    --mode clausify
% 7.62/1.49  --stdin                                 false
% 7.62/1.49  --stats_out                             all
% 7.62/1.49  
% 7.62/1.49  ------ General Options
% 7.62/1.49  
% 7.62/1.49  --fof                                   false
% 7.62/1.49  --time_out_real                         305.
% 7.62/1.49  --time_out_virtual                      -1.
% 7.62/1.49  --symbol_type_check                     false
% 7.62/1.49  --clausify_out                          false
% 7.62/1.49  --sig_cnt_out                           false
% 7.62/1.49  --trig_cnt_out                          false
% 7.62/1.49  --trig_cnt_out_tolerance                1.
% 7.62/1.49  --trig_cnt_out_sk_spl                   false
% 7.62/1.49  --abstr_cl_out                          false
% 7.62/1.49  
% 7.62/1.49  ------ Global Options
% 7.62/1.49  
% 7.62/1.49  --schedule                              default
% 7.62/1.49  --add_important_lit                     false
% 7.62/1.49  --prop_solver_per_cl                    1000
% 7.62/1.49  --min_unsat_core                        false
% 7.62/1.49  --soft_assumptions                      false
% 7.62/1.49  --soft_lemma_size                       3
% 7.62/1.49  --prop_impl_unit_size                   0
% 7.62/1.49  --prop_impl_unit                        []
% 7.62/1.49  --share_sel_clauses                     true
% 7.62/1.49  --reset_solvers                         false
% 7.62/1.49  --bc_imp_inh                            [conj_cone]
% 7.62/1.49  --conj_cone_tolerance                   3.
% 7.62/1.49  --extra_neg_conj                        none
% 7.62/1.49  --large_theory_mode                     true
% 7.62/1.49  --prolific_symb_bound                   200
% 7.62/1.49  --lt_threshold                          2000
% 7.62/1.49  --clause_weak_htbl                      true
% 7.62/1.49  --gc_record_bc_elim                     false
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing Options
% 7.62/1.49  
% 7.62/1.49  --preprocessing_flag                    true
% 7.62/1.49  --time_out_prep_mult                    0.1
% 7.62/1.49  --splitting_mode                        input
% 7.62/1.49  --splitting_grd                         true
% 7.62/1.49  --splitting_cvd                         false
% 7.62/1.49  --splitting_cvd_svl                     false
% 7.62/1.49  --splitting_nvd                         32
% 7.62/1.49  --sub_typing                            true
% 7.62/1.49  --prep_gs_sim                           true
% 7.62/1.49  --prep_unflatten                        true
% 7.62/1.49  --prep_res_sim                          true
% 7.62/1.49  --prep_upred                            true
% 7.62/1.49  --prep_sem_filter                       exhaustive
% 7.62/1.49  --prep_sem_filter_out                   false
% 7.62/1.49  --pred_elim                             true
% 7.62/1.49  --res_sim_input                         true
% 7.62/1.49  --eq_ax_congr_red                       true
% 7.62/1.49  --pure_diseq_elim                       true
% 7.62/1.49  --brand_transform                       false
% 7.62/1.49  --non_eq_to_eq                          false
% 7.62/1.49  --prep_def_merge                        true
% 7.62/1.49  --prep_def_merge_prop_impl              false
% 7.62/1.49  --prep_def_merge_mbd                    true
% 7.62/1.49  --prep_def_merge_tr_red                 false
% 7.62/1.49  --prep_def_merge_tr_cl                  false
% 7.62/1.49  --smt_preprocessing                     true
% 7.62/1.49  --smt_ac_axioms                         fast
% 7.62/1.49  --preprocessed_out                      false
% 7.62/1.49  --preprocessed_stats                    false
% 7.62/1.49  
% 7.62/1.49  ------ Abstraction refinement Options
% 7.62/1.49  
% 7.62/1.49  --abstr_ref                             []
% 7.62/1.49  --abstr_ref_prep                        false
% 7.62/1.49  --abstr_ref_until_sat                   false
% 7.62/1.49  --abstr_ref_sig_restrict                funpre
% 7.62/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.62/1.49  --abstr_ref_under                       []
% 7.62/1.49  
% 7.62/1.49  ------ SAT Options
% 7.62/1.49  
% 7.62/1.49  --sat_mode                              false
% 7.62/1.49  --sat_fm_restart_options                ""
% 7.62/1.49  --sat_gr_def                            false
% 7.62/1.49  --sat_epr_types                         true
% 7.62/1.49  --sat_non_cyclic_types                  false
% 7.62/1.49  --sat_finite_models                     false
% 7.62/1.49  --sat_fm_lemmas                         false
% 7.62/1.49  --sat_fm_prep                           false
% 7.62/1.49  --sat_fm_uc_incr                        true
% 7.62/1.49  --sat_out_model                         small
% 7.62/1.49  --sat_out_clauses                       false
% 7.62/1.49  
% 7.62/1.49  ------ QBF Options
% 7.62/1.49  
% 7.62/1.49  --qbf_mode                              false
% 7.62/1.49  --qbf_elim_univ                         false
% 7.62/1.49  --qbf_dom_inst                          none
% 7.62/1.49  --qbf_dom_pre_inst                      false
% 7.62/1.49  --qbf_sk_in                             false
% 7.62/1.49  --qbf_pred_elim                         true
% 7.62/1.49  --qbf_split                             512
% 7.62/1.49  
% 7.62/1.49  ------ BMC1 Options
% 7.62/1.49  
% 7.62/1.49  --bmc1_incremental                      false
% 7.62/1.49  --bmc1_axioms                           reachable_all
% 7.62/1.49  --bmc1_min_bound                        0
% 7.62/1.49  --bmc1_max_bound                        -1
% 7.62/1.49  --bmc1_max_bound_default                -1
% 7.62/1.49  --bmc1_symbol_reachability              true
% 7.62/1.49  --bmc1_property_lemmas                  false
% 7.62/1.49  --bmc1_k_induction                      false
% 7.62/1.49  --bmc1_non_equiv_states                 false
% 7.62/1.49  --bmc1_deadlock                         false
% 7.62/1.49  --bmc1_ucm                              false
% 7.62/1.49  --bmc1_add_unsat_core                   none
% 7.62/1.49  --bmc1_unsat_core_children              false
% 7.62/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.62/1.49  --bmc1_out_stat                         full
% 7.62/1.49  --bmc1_ground_init                      false
% 7.62/1.49  --bmc1_pre_inst_next_state              false
% 7.62/1.49  --bmc1_pre_inst_state                   false
% 7.62/1.49  --bmc1_pre_inst_reach_state             false
% 7.62/1.49  --bmc1_out_unsat_core                   false
% 7.62/1.49  --bmc1_aig_witness_out                  false
% 7.62/1.49  --bmc1_verbose                          false
% 7.62/1.49  --bmc1_dump_clauses_tptp                false
% 7.62/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.62/1.49  --bmc1_dump_file                        -
% 7.62/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.62/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.62/1.49  --bmc1_ucm_extend_mode                  1
% 7.62/1.49  --bmc1_ucm_init_mode                    2
% 7.62/1.49  --bmc1_ucm_cone_mode                    none
% 7.62/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.62/1.49  --bmc1_ucm_relax_model                  4
% 7.62/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.62/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.62/1.49  --bmc1_ucm_layered_model                none
% 7.62/1.49  --bmc1_ucm_max_lemma_size               10
% 7.62/1.49  
% 7.62/1.49  ------ AIG Options
% 7.62/1.49  
% 7.62/1.49  --aig_mode                              false
% 7.62/1.49  
% 7.62/1.49  ------ Instantiation Options
% 7.62/1.49  
% 7.62/1.49  --instantiation_flag                    true
% 7.62/1.49  --inst_sos_flag                         false
% 7.62/1.49  --inst_sos_phase                        true
% 7.62/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.62/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.62/1.49  --inst_lit_sel_side                     num_symb
% 7.62/1.49  --inst_solver_per_active                1400
% 7.62/1.49  --inst_solver_calls_frac                1.
% 7.62/1.49  --inst_passive_queue_type               priority_queues
% 7.62/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.62/1.49  --inst_passive_queues_freq              [25;2]
% 7.62/1.49  --inst_dismatching                      true
% 7.62/1.49  --inst_eager_unprocessed_to_passive     true
% 7.62/1.49  --inst_prop_sim_given                   true
% 7.62/1.49  --inst_prop_sim_new                     false
% 7.62/1.49  --inst_subs_new                         false
% 7.62/1.49  --inst_eq_res_simp                      false
% 7.62/1.49  --inst_subs_given                       false
% 7.62/1.49  --inst_orphan_elimination               true
% 7.62/1.49  --inst_learning_loop_flag               true
% 7.62/1.49  --inst_learning_start                   3000
% 7.62/1.49  --inst_learning_factor                  2
% 7.62/1.49  --inst_start_prop_sim_after_learn       3
% 7.62/1.49  --inst_sel_renew                        solver
% 7.62/1.49  --inst_lit_activity_flag                true
% 7.62/1.49  --inst_restr_to_given                   false
% 7.62/1.49  --inst_activity_threshold               500
% 7.62/1.49  --inst_out_proof                        true
% 7.62/1.49  
% 7.62/1.49  ------ Resolution Options
% 7.62/1.49  
% 7.62/1.49  --resolution_flag                       true
% 7.62/1.49  --res_lit_sel                           adaptive
% 7.62/1.49  --res_lit_sel_side                      none
% 7.62/1.49  --res_ordering                          kbo
% 7.62/1.49  --res_to_prop_solver                    active
% 7.62/1.49  --res_prop_simpl_new                    false
% 7.62/1.49  --res_prop_simpl_given                  true
% 7.62/1.49  --res_passive_queue_type                priority_queues
% 7.62/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.62/1.49  --res_passive_queues_freq               [15;5]
% 7.62/1.49  --res_forward_subs                      full
% 7.62/1.49  --res_backward_subs                     full
% 7.62/1.49  --res_forward_subs_resolution           true
% 7.62/1.49  --res_backward_subs_resolution          true
% 7.62/1.49  --res_orphan_elimination                true
% 7.62/1.49  --res_time_limit                        2.
% 7.62/1.49  --res_out_proof                         true
% 7.62/1.49  
% 7.62/1.49  ------ Superposition Options
% 7.62/1.49  
% 7.62/1.49  --superposition_flag                    true
% 7.62/1.49  --sup_passive_queue_type                priority_queues
% 7.62/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.62/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.62/1.49  --demod_completeness_check              fast
% 7.62/1.49  --demod_use_ground                      true
% 7.62/1.49  --sup_to_prop_solver                    passive
% 7.62/1.49  --sup_prop_simpl_new                    true
% 7.62/1.49  --sup_prop_simpl_given                  true
% 7.62/1.49  --sup_fun_splitting                     false
% 7.62/1.49  --sup_smt_interval                      50000
% 7.62/1.49  
% 7.62/1.49  ------ Superposition Simplification Setup
% 7.62/1.49  
% 7.62/1.49  --sup_indices_passive                   []
% 7.62/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.62/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.49  --sup_full_bw                           [BwDemod]
% 7.62/1.49  --sup_immed_triv                        [TrivRules]
% 7.62/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.49  --sup_immed_bw_main                     []
% 7.62/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.62/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.62/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.62/1.49  
% 7.62/1.49  ------ Combination Options
% 7.62/1.49  
% 7.62/1.49  --comb_res_mult                         3
% 7.62/1.49  --comb_sup_mult                         2
% 7.62/1.49  --comb_inst_mult                        10
% 7.62/1.49  
% 7.62/1.49  ------ Debug Options
% 7.62/1.49  
% 7.62/1.49  --dbg_backtrace                         false
% 7.62/1.49  --dbg_dump_prop_clauses                 false
% 7.62/1.49  --dbg_dump_prop_clauses_file            -
% 7.62/1.49  --dbg_out_stat                          false
% 7.62/1.49  ------ Parsing...
% 7.62/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  ------ Proving...
% 7.62/1.49  ------ Problem Properties 
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  clauses                                 33
% 7.62/1.49  conjectures                             3
% 7.62/1.49  EPR                                     4
% 7.62/1.49  Horn                                    25
% 7.62/1.49  unary                                   6
% 7.62/1.49  binary                                  13
% 7.62/1.49  lits                                    81
% 7.62/1.49  lits eq                                 42
% 7.62/1.49  fd_pure                                 0
% 7.62/1.49  fd_pseudo                               0
% 7.62/1.49  fd_cond                                 4
% 7.62/1.49  fd_pseudo_cond                          1
% 7.62/1.49  AC symbols                              0
% 7.62/1.49  
% 7.62/1.49  ------ Schedule dynamic 5 is on 
% 7.62/1.49  
% 7.62/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ 
% 7.62/1.49  Current options:
% 7.62/1.49  ------ 
% 7.62/1.49  
% 7.62/1.49  ------ Input Options
% 7.62/1.49  
% 7.62/1.49  --out_options                           all
% 7.62/1.49  --tptp_safe_out                         true
% 7.62/1.49  --problem_path                          ""
% 7.62/1.49  --include_path                          ""
% 7.62/1.49  --clausifier                            res/vclausify_rel
% 7.62/1.49  --clausifier_options                    --mode clausify
% 7.62/1.49  --stdin                                 false
% 7.62/1.49  --stats_out                             all
% 7.62/1.49  
% 7.62/1.49  ------ General Options
% 7.62/1.49  
% 7.62/1.49  --fof                                   false
% 7.62/1.49  --time_out_real                         305.
% 7.62/1.49  --time_out_virtual                      -1.
% 7.62/1.49  --symbol_type_check                     false
% 7.62/1.49  --clausify_out                          false
% 7.62/1.49  --sig_cnt_out                           false
% 7.62/1.49  --trig_cnt_out                          false
% 7.62/1.49  --trig_cnt_out_tolerance                1.
% 7.62/1.49  --trig_cnt_out_sk_spl                   false
% 7.62/1.49  --abstr_cl_out                          false
% 7.62/1.49  
% 7.62/1.49  ------ Global Options
% 7.62/1.49  
% 7.62/1.49  --schedule                              default
% 7.62/1.49  --add_important_lit                     false
% 7.62/1.49  --prop_solver_per_cl                    1000
% 7.62/1.49  --min_unsat_core                        false
% 7.62/1.49  --soft_assumptions                      false
% 7.62/1.49  --soft_lemma_size                       3
% 7.62/1.49  --prop_impl_unit_size                   0
% 7.62/1.49  --prop_impl_unit                        []
% 7.62/1.49  --share_sel_clauses                     true
% 7.62/1.49  --reset_solvers                         false
% 7.62/1.49  --bc_imp_inh                            [conj_cone]
% 7.62/1.49  --conj_cone_tolerance                   3.
% 7.62/1.49  --extra_neg_conj                        none
% 7.62/1.49  --large_theory_mode                     true
% 7.62/1.49  --prolific_symb_bound                   200
% 7.62/1.49  --lt_threshold                          2000
% 7.62/1.49  --clause_weak_htbl                      true
% 7.62/1.49  --gc_record_bc_elim                     false
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing Options
% 7.62/1.49  
% 7.62/1.49  --preprocessing_flag                    true
% 7.62/1.49  --time_out_prep_mult                    0.1
% 7.62/1.49  --splitting_mode                        input
% 7.62/1.49  --splitting_grd                         true
% 7.62/1.49  --splitting_cvd                         false
% 7.62/1.49  --splitting_cvd_svl                     false
% 7.62/1.49  --splitting_nvd                         32
% 7.62/1.49  --sub_typing                            true
% 7.62/1.49  --prep_gs_sim                           true
% 7.62/1.49  --prep_unflatten                        true
% 7.62/1.49  --prep_res_sim                          true
% 7.62/1.49  --prep_upred                            true
% 7.62/1.49  --prep_sem_filter                       exhaustive
% 7.62/1.49  --prep_sem_filter_out                   false
% 7.62/1.49  --pred_elim                             true
% 7.62/1.49  --res_sim_input                         true
% 7.62/1.49  --eq_ax_congr_red                       true
% 7.62/1.49  --pure_diseq_elim                       true
% 7.62/1.49  --brand_transform                       false
% 7.62/1.49  --non_eq_to_eq                          false
% 7.62/1.49  --prep_def_merge                        true
% 7.62/1.49  --prep_def_merge_prop_impl              false
% 7.62/1.49  --prep_def_merge_mbd                    true
% 7.62/1.49  --prep_def_merge_tr_red                 false
% 7.62/1.49  --prep_def_merge_tr_cl                  false
% 7.62/1.49  --smt_preprocessing                     true
% 7.62/1.49  --smt_ac_axioms                         fast
% 7.62/1.49  --preprocessed_out                      false
% 7.62/1.49  --preprocessed_stats                    false
% 7.62/1.49  
% 7.62/1.49  ------ Abstraction refinement Options
% 7.62/1.49  
% 7.62/1.49  --abstr_ref                             []
% 7.62/1.49  --abstr_ref_prep                        false
% 7.62/1.49  --abstr_ref_until_sat                   false
% 7.62/1.49  --abstr_ref_sig_restrict                funpre
% 7.62/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.62/1.49  --abstr_ref_under                       []
% 7.62/1.49  
% 7.62/1.49  ------ SAT Options
% 7.62/1.49  
% 7.62/1.49  --sat_mode                              false
% 7.62/1.49  --sat_fm_restart_options                ""
% 7.62/1.49  --sat_gr_def                            false
% 7.62/1.49  --sat_epr_types                         true
% 7.62/1.49  --sat_non_cyclic_types                  false
% 7.62/1.49  --sat_finite_models                     false
% 7.62/1.49  --sat_fm_lemmas                         false
% 7.62/1.49  --sat_fm_prep                           false
% 7.62/1.49  --sat_fm_uc_incr                        true
% 7.62/1.49  --sat_out_model                         small
% 7.62/1.49  --sat_out_clauses                       false
% 7.62/1.49  
% 7.62/1.49  ------ QBF Options
% 7.62/1.49  
% 7.62/1.49  --qbf_mode                              false
% 7.62/1.49  --qbf_elim_univ                         false
% 7.62/1.49  --qbf_dom_inst                          none
% 7.62/1.49  --qbf_dom_pre_inst                      false
% 7.62/1.49  --qbf_sk_in                             false
% 7.62/1.49  --qbf_pred_elim                         true
% 7.62/1.49  --qbf_split                             512
% 7.62/1.49  
% 7.62/1.49  ------ BMC1 Options
% 7.62/1.49  
% 7.62/1.49  --bmc1_incremental                      false
% 7.62/1.49  --bmc1_axioms                           reachable_all
% 7.62/1.49  --bmc1_min_bound                        0
% 7.62/1.49  --bmc1_max_bound                        -1
% 7.62/1.49  --bmc1_max_bound_default                -1
% 7.62/1.49  --bmc1_symbol_reachability              true
% 7.62/1.49  --bmc1_property_lemmas                  false
% 7.62/1.49  --bmc1_k_induction                      false
% 7.62/1.49  --bmc1_non_equiv_states                 false
% 7.62/1.49  --bmc1_deadlock                         false
% 7.62/1.49  --bmc1_ucm                              false
% 7.62/1.49  --bmc1_add_unsat_core                   none
% 7.62/1.49  --bmc1_unsat_core_children              false
% 7.62/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.62/1.49  --bmc1_out_stat                         full
% 7.62/1.49  --bmc1_ground_init                      false
% 7.62/1.49  --bmc1_pre_inst_next_state              false
% 7.62/1.49  --bmc1_pre_inst_state                   false
% 7.62/1.49  --bmc1_pre_inst_reach_state             false
% 7.62/1.49  --bmc1_out_unsat_core                   false
% 7.62/1.49  --bmc1_aig_witness_out                  false
% 7.62/1.49  --bmc1_verbose                          false
% 7.62/1.49  --bmc1_dump_clauses_tptp                false
% 7.62/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.62/1.49  --bmc1_dump_file                        -
% 7.62/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.62/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.62/1.49  --bmc1_ucm_extend_mode                  1
% 7.62/1.49  --bmc1_ucm_init_mode                    2
% 7.62/1.49  --bmc1_ucm_cone_mode                    none
% 7.62/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.62/1.49  --bmc1_ucm_relax_model                  4
% 7.62/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.62/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.62/1.49  --bmc1_ucm_layered_model                none
% 7.62/1.49  --bmc1_ucm_max_lemma_size               10
% 7.62/1.49  
% 7.62/1.49  ------ AIG Options
% 7.62/1.49  
% 7.62/1.49  --aig_mode                              false
% 7.62/1.49  
% 7.62/1.49  ------ Instantiation Options
% 7.62/1.49  
% 7.62/1.49  --instantiation_flag                    true
% 7.62/1.49  --inst_sos_flag                         false
% 7.62/1.49  --inst_sos_phase                        true
% 7.62/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.62/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.62/1.49  --inst_lit_sel_side                     none
% 7.62/1.49  --inst_solver_per_active                1400
% 7.62/1.49  --inst_solver_calls_frac                1.
% 7.62/1.49  --inst_passive_queue_type               priority_queues
% 7.62/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.62/1.49  --inst_passive_queues_freq              [25;2]
% 7.62/1.49  --inst_dismatching                      true
% 7.62/1.49  --inst_eager_unprocessed_to_passive     true
% 7.62/1.49  --inst_prop_sim_given                   true
% 7.62/1.49  --inst_prop_sim_new                     false
% 7.62/1.49  --inst_subs_new                         false
% 7.62/1.49  --inst_eq_res_simp                      false
% 7.62/1.49  --inst_subs_given                       false
% 7.62/1.49  --inst_orphan_elimination               true
% 7.62/1.49  --inst_learning_loop_flag               true
% 7.62/1.49  --inst_learning_start                   3000
% 7.62/1.49  --inst_learning_factor                  2
% 7.62/1.49  --inst_start_prop_sim_after_learn       3
% 7.62/1.49  --inst_sel_renew                        solver
% 7.62/1.49  --inst_lit_activity_flag                true
% 7.62/1.49  --inst_restr_to_given                   false
% 7.62/1.49  --inst_activity_threshold               500
% 7.62/1.49  --inst_out_proof                        true
% 7.62/1.49  
% 7.62/1.49  ------ Resolution Options
% 7.62/1.49  
% 7.62/1.49  --resolution_flag                       false
% 7.62/1.49  --res_lit_sel                           adaptive
% 7.62/1.49  --res_lit_sel_side                      none
% 7.62/1.49  --res_ordering                          kbo
% 7.62/1.49  --res_to_prop_solver                    active
% 7.62/1.49  --res_prop_simpl_new                    false
% 7.62/1.49  --res_prop_simpl_given                  true
% 7.62/1.49  --res_passive_queue_type                priority_queues
% 7.62/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.62/1.49  --res_passive_queues_freq               [15;5]
% 7.62/1.49  --res_forward_subs                      full
% 7.62/1.49  --res_backward_subs                     full
% 7.62/1.49  --res_forward_subs_resolution           true
% 7.62/1.49  --res_backward_subs_resolution          true
% 7.62/1.49  --res_orphan_elimination                true
% 7.62/1.49  --res_time_limit                        2.
% 7.62/1.49  --res_out_proof                         true
% 7.62/1.49  
% 7.62/1.49  ------ Superposition Options
% 7.62/1.49  
% 7.62/1.49  --superposition_flag                    true
% 7.62/1.49  --sup_passive_queue_type                priority_queues
% 7.62/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.62/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.62/1.49  --demod_completeness_check              fast
% 7.62/1.49  --demod_use_ground                      true
% 7.62/1.49  --sup_to_prop_solver                    passive
% 7.62/1.49  --sup_prop_simpl_new                    true
% 7.62/1.49  --sup_prop_simpl_given                  true
% 7.62/1.49  --sup_fun_splitting                     false
% 7.62/1.49  --sup_smt_interval                      50000
% 7.62/1.49  
% 7.62/1.49  ------ Superposition Simplification Setup
% 7.62/1.49  
% 7.62/1.49  --sup_indices_passive                   []
% 7.62/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.62/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.49  --sup_full_bw                           [BwDemod]
% 7.62/1.49  --sup_immed_triv                        [TrivRules]
% 7.62/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.49  --sup_immed_bw_main                     []
% 7.62/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.62/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.62/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.62/1.49  
% 7.62/1.49  ------ Combination Options
% 7.62/1.49  
% 7.62/1.49  --comb_res_mult                         3
% 7.62/1.49  --comb_sup_mult                         2
% 7.62/1.49  --comb_inst_mult                        10
% 7.62/1.49  
% 7.62/1.49  ------ Debug Options
% 7.62/1.49  
% 7.62/1.49  --dbg_backtrace                         false
% 7.62/1.49  --dbg_dump_prop_clauses                 false
% 7.62/1.49  --dbg_dump_prop_clauses_file            -
% 7.62/1.49  --dbg_out_stat                          false
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  % SZS status Theorem for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49   Resolution empty clause
% 7.62/1.49  
% 7.62/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  fof(f14,axiom,(
% 7.62/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f29,plain,(
% 7.62/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.62/1.49    inference(ennf_transformation,[],[f14])).
% 7.62/1.49  
% 7.62/1.49  fof(f30,plain,(
% 7.62/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.62/1.49    inference(flattening,[],[f29])).
% 7.62/1.49  
% 7.62/1.49  fof(f42,plain,(
% 7.62/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.62/1.49    inference(nnf_transformation,[],[f30])).
% 7.62/1.49  
% 7.62/1.49  fof(f63,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f42])).
% 7.62/1.49  
% 7.62/1.49  fof(f17,conjecture,(
% 7.62/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f18,negated_conjecture,(
% 7.62/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 7.62/1.49    inference(negated_conjecture,[],[f17])).
% 7.62/1.49  
% 7.62/1.49  fof(f35,plain,(
% 7.62/1.49    ? [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.62/1.49    inference(ennf_transformation,[],[f18])).
% 7.62/1.49  
% 7.62/1.49  fof(f36,plain,(
% 7.62/1.49    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.62/1.49    inference(flattening,[],[f35])).
% 7.62/1.49  
% 7.62/1.49  fof(f43,plain,(
% 7.62/1.49    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) != sK0 & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f44,plain,(
% 7.62/1.49    k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) != sK0 & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.62/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f43])).
% 7.62/1.49  
% 7.62/1.49  fof(f75,plain,(
% 7.62/1.49    v1_funct_2(sK2,sK0,sK1)),
% 7.62/1.49    inference(cnf_transformation,[],[f44])).
% 7.62/1.49  
% 7.62/1.49  fof(f76,plain,(
% 7.62/1.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.62/1.49    inference(cnf_transformation,[],[f44])).
% 7.62/1.49  
% 7.62/1.49  fof(f10,axiom,(
% 7.62/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f25,plain,(
% 7.62/1.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.62/1.49    inference(ennf_transformation,[],[f10])).
% 7.62/1.49  
% 7.62/1.49  fof(f58,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f25])).
% 7.62/1.49  
% 7.62/1.49  fof(f16,axiom,(
% 7.62/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f33,plain,(
% 7.62/1.49    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.62/1.49    inference(ennf_transformation,[],[f16])).
% 7.62/1.49  
% 7.62/1.49  fof(f34,plain,(
% 7.62/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.62/1.49    inference(flattening,[],[f33])).
% 7.62/1.49  
% 7.62/1.49  fof(f73,plain,(
% 7.62/1.49    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f34])).
% 7.62/1.49  
% 7.62/1.49  fof(f74,plain,(
% 7.62/1.49    v1_funct_1(sK2)),
% 7.62/1.49    inference(cnf_transformation,[],[f44])).
% 7.62/1.49  
% 7.62/1.49  fof(f8,axiom,(
% 7.62/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f23,plain,(
% 7.62/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.62/1.49    inference(ennf_transformation,[],[f8])).
% 7.62/1.49  
% 7.62/1.49  fof(f56,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f23])).
% 7.62/1.49  
% 7.62/1.49  fof(f1,axiom,(
% 7.62/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f37,plain,(
% 7.62/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.62/1.49    inference(nnf_transformation,[],[f1])).
% 7.62/1.49  
% 7.62/1.49  fof(f38,plain,(
% 7.62/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.62/1.49    inference(flattening,[],[f37])).
% 7.62/1.49  
% 7.62/1.49  fof(f46,plain,(
% 7.62/1.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.62/1.49    inference(cnf_transformation,[],[f38])).
% 7.62/1.49  
% 7.62/1.49  fof(f79,plain,(
% 7.62/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.62/1.49    inference(equality_resolution,[],[f46])).
% 7.62/1.49  
% 7.62/1.49  fof(f72,plain,(
% 7.62/1.49    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f34])).
% 7.62/1.49  
% 7.62/1.49  fof(f65,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f42])).
% 7.62/1.49  
% 7.62/1.49  fof(f15,axiom,(
% 7.62/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f31,plain,(
% 7.62/1.49    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.62/1.49    inference(ennf_transformation,[],[f15])).
% 7.62/1.49  
% 7.62/1.49  fof(f32,plain,(
% 7.62/1.49    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.62/1.49    inference(flattening,[],[f31])).
% 7.62/1.49  
% 7.62/1.49  fof(f69,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f32])).
% 7.62/1.49  
% 7.62/1.49  fof(f3,axiom,(
% 7.62/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f39,plain,(
% 7.62/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.62/1.49    inference(nnf_transformation,[],[f3])).
% 7.62/1.49  
% 7.62/1.49  fof(f40,plain,(
% 7.62/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.62/1.49    inference(flattening,[],[f39])).
% 7.62/1.49  
% 7.62/1.49  fof(f49,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f40])).
% 7.62/1.49  
% 7.62/1.49  fof(f50,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.62/1.49    inference(cnf_transformation,[],[f40])).
% 7.62/1.49  
% 7.62/1.49  fof(f82,plain,(
% 7.62/1.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.62/1.49    inference(equality_resolution,[],[f50])).
% 7.62/1.49  
% 7.62/1.49  fof(f5,axiom,(
% 7.62/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f41,plain,(
% 7.62/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.62/1.49    inference(nnf_transformation,[],[f5])).
% 7.62/1.49  
% 7.62/1.49  fof(f53,plain,(
% 7.62/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f41])).
% 7.62/1.49  
% 7.62/1.49  fof(f47,plain,(
% 7.62/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f38])).
% 7.62/1.49  
% 7.62/1.49  fof(f7,axiom,(
% 7.62/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f21,plain,(
% 7.62/1.49    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.62/1.49    inference(ennf_transformation,[],[f7])).
% 7.62/1.49  
% 7.62/1.49  fof(f22,plain,(
% 7.62/1.49    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.62/1.49    inference(flattening,[],[f21])).
% 7.62/1.49  
% 7.62/1.49  fof(f55,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f22])).
% 7.62/1.49  
% 7.62/1.49  fof(f11,axiom,(
% 7.62/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f26,plain,(
% 7.62/1.49    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.62/1.49    inference(ennf_transformation,[],[f11])).
% 7.62/1.49  
% 7.62/1.49  fof(f59,plain,(
% 7.62/1.49    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f26])).
% 7.62/1.49  
% 7.62/1.49  fof(f9,axiom,(
% 7.62/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f24,plain,(
% 7.62/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.62/1.49    inference(ennf_transformation,[],[f9])).
% 7.62/1.49  
% 7.62/1.49  fof(f57,plain,(
% 7.62/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f24])).
% 7.62/1.49  
% 7.62/1.49  fof(f4,axiom,(
% 7.62/1.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f52,plain,(
% 7.62/1.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f4])).
% 7.62/1.49  
% 7.62/1.49  fof(f12,axiom,(
% 7.62/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f27,plain,(
% 7.62/1.49    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.62/1.49    inference(ennf_transformation,[],[f12])).
% 7.62/1.49  
% 7.62/1.49  fof(f60,plain,(
% 7.62/1.49    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f27])).
% 7.62/1.49  
% 7.62/1.49  fof(f78,plain,(
% 7.62/1.49    k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) != sK0),
% 7.62/1.49    inference(cnf_transformation,[],[f44])).
% 7.62/1.49  
% 7.62/1.49  fof(f13,axiom,(
% 7.62/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f28,plain,(
% 7.62/1.49    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.62/1.49    inference(ennf_transformation,[],[f13])).
% 7.62/1.49  
% 7.62/1.49  fof(f62,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f28])).
% 7.62/1.49  
% 7.62/1.49  fof(f51,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.62/1.49    inference(cnf_transformation,[],[f40])).
% 7.62/1.49  
% 7.62/1.49  fof(f81,plain,(
% 7.62/1.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.62/1.49    inference(equality_resolution,[],[f51])).
% 7.62/1.49  
% 7.62/1.49  fof(f67,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f42])).
% 7.62/1.49  
% 7.62/1.49  fof(f85,plain,(
% 7.62/1.49    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.62/1.49    inference(equality_resolution,[],[f67])).
% 7.62/1.49  
% 7.62/1.49  fof(f77,plain,(
% 7.62/1.49    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 7.62/1.49    inference(cnf_transformation,[],[f44])).
% 7.62/1.49  
% 7.62/1.49  fof(f64,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f42])).
% 7.62/1.49  
% 7.62/1.49  fof(f87,plain,(
% 7.62/1.49    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.62/1.49    inference(equality_resolution,[],[f64])).
% 7.62/1.49  
% 7.62/1.49  cnf(c_23,plain,
% 7.62/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.62/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.62/1.49      | k1_xboole_0 = X2 ),
% 7.62/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_32,negated_conjecture,
% 7.62/1.49      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.62/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_729,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.62/1.49      | sK2 != X0
% 7.62/1.49      | sK1 != X2
% 7.62/1.49      | sK0 != X1
% 7.62/1.49      | k1_xboole_0 = X2 ),
% 7.62/1.49      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_730,plain,
% 7.62/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.62/1.49      | k1_relset_1(sK0,sK1,sK2) = sK0
% 7.62/1.49      | k1_xboole_0 = sK1 ),
% 7.62/1.49      inference(unflattening,[status(thm)],[c_729]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_31,negated_conjecture,
% 7.62/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.62/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_732,plain,
% 7.62/1.49      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 7.62/1.49      inference(global_propositional_subsumption,[status(thm)],[c_730,c_31]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1966,plain,
% 7.62/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_13,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1971,plain,
% 7.62/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.62/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3648,plain,
% 7.62/1.49      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_1966,c_1971]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3750,plain,
% 7.62/1.49      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_732,c_3648]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_26,plain,
% 7.62/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.62/1.49      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.62/1.49      | ~ v1_relat_1(X0)
% 7.62/1.49      | ~ v1_funct_1(X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_33,negated_conjecture,
% 7.62/1.49      ( v1_funct_1(sK2) ),
% 7.62/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_481,plain,
% 7.62/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.62/1.49      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.62/1.49      | ~ v1_relat_1(X0)
% 7.62/1.49      | sK2 != X0 ),
% 7.62/1.49      inference(resolution_lifted,[status(thm)],[c_26,c_33]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_482,plain,
% 7.62/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
% 7.62/1.49      | ~ r1_tarski(k2_relat_1(sK2),X0)
% 7.62/1.49      | ~ v1_relat_1(sK2) ),
% 7.62/1.49      inference(unflattening,[status(thm)],[c_481]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1964,plain,
% 7.62/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 7.62/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_482]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_36,plain,
% 7.62/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_483,plain,
% 7.62/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 7.62/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_482]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_11,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2232,plain,
% 7.62/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.62/1.49      | v1_relat_1(sK2) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2233,plain,
% 7.62/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.62/1.49      | v1_relat_1(sK2) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_2232]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2291,plain,
% 7.62/1.49      ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 7.62/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_1964,c_36,c_483,c_2233]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2292,plain,
% 7.62/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
% 7.62/1.49      inference(renaming,[status(thm)],[c_2291]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3829,plain,
% 7.62/1.49      ( sK1 = k1_xboole_0
% 7.62/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_3750,c_2292]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f79]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1978,plain,
% 7.62/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_27,plain,
% 7.62/1.49      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.62/1.49      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.62/1.49      | ~ v1_relat_1(X0)
% 7.62/1.49      | ~ v1_funct_1(X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_466,plain,
% 7.62/1.49      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.62/1.49      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.62/1.49      | ~ v1_relat_1(X0)
% 7.62/1.49      | sK2 != X0 ),
% 7.62/1.49      inference(resolution_lifted,[status(thm)],[c_27,c_33]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_467,plain,
% 7.62/1.49      ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
% 7.62/1.49      | ~ r1_tarski(k2_relat_1(sK2),X0)
% 7.62/1.49      | ~ v1_relat_1(sK2) ),
% 7.62/1.49      inference(unflattening,[status(thm)],[c_466]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_740,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | ~ r1_tarski(k2_relat_1(sK2),X3)
% 7.62/1.49      | ~ v1_relat_1(sK2)
% 7.62/1.49      | X3 != X2
% 7.62/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.62/1.49      | k1_relat_1(sK2) != X1
% 7.62/1.49      | sK2 != X0
% 7.62/1.49      | k1_xboole_0 = X2 ),
% 7.62/1.49      inference(resolution_lifted,[status(thm)],[c_23,c_467]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_741,plain,
% 7.62/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
% 7.62/1.49      | ~ r1_tarski(k2_relat_1(sK2),X0)
% 7.62/1.49      | ~ v1_relat_1(sK2)
% 7.62/1.49      | k1_relset_1(k1_relat_1(sK2),X0,sK2) = k1_relat_1(sK2)
% 7.62/1.49      | k1_xboole_0 = X0 ),
% 7.62/1.49      inference(unflattening,[status(thm)],[c_740]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_745,plain,
% 7.62/1.49      ( ~ r1_tarski(k2_relat_1(sK2),X0)
% 7.62/1.49      | ~ v1_relat_1(sK2)
% 7.62/1.49      | k1_relset_1(k1_relat_1(sK2),X0,sK2) = k1_relat_1(sK2)
% 7.62/1.49      | k1_xboole_0 = X0 ),
% 7.62/1.49      inference(global_propositional_subsumption,[status(thm)],[c_741,c_482]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1958,plain,
% 7.62/1.49      ( k1_relset_1(k1_relat_1(sK2),X0,sK2) = k1_relat_1(sK2)
% 7.62/1.49      | k1_xboole_0 = X0
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 7.62/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_745]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_742,plain,
% 7.62/1.49      ( k1_relset_1(k1_relat_1(sK2),X0,sK2) = k1_relat_1(sK2)
% 7.62/1.49      | k1_xboole_0 = X0
% 7.62/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) != iProver_top
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 7.62/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2669,plain,
% 7.62/1.49      ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 7.62/1.49      | k1_xboole_0 = X0
% 7.62/1.49      | k1_relset_1(k1_relat_1(sK2),X0,sK2) = k1_relat_1(sK2) ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_1958,c_36,c_483,c_742,c_2233]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2670,plain,
% 7.62/1.49      ( k1_relset_1(k1_relat_1(sK2),X0,sK2) = k1_relat_1(sK2)
% 7.62/1.49      | k1_xboole_0 = X0
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
% 7.62/1.49      inference(renaming,[status(thm)],[c_2669]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2676,plain,
% 7.62/1.49      ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2)
% 7.62/1.49      | k2_relat_1(sK2) = k1_xboole_0 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_1978,c_2670]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3826,plain,
% 7.62/1.49      ( k1_relset_1(sK0,k2_relat_1(sK2),sK2) = k1_relat_1(sK2)
% 7.62/1.49      | k2_relat_1(sK2) = k1_xboole_0
% 7.62/1.49      | sK1 = k1_xboole_0 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_3750,c_2676]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_21,plain,
% 7.62/1.49      ( v1_funct_2(X0,X1,X2)
% 7.62/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | k1_relset_1(X1,X2,X0) != X1
% 7.62/1.49      | k1_xboole_0 = X2 ),
% 7.62/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_25,plain,
% 7.62/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.62/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | ~ v1_funct_1(X0)
% 7.62/1.49      | k8_relset_1(X1,X2,X0,X2) = X1
% 7.62/1.49      | k1_xboole_0 = X2 ),
% 7.62/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_496,plain,
% 7.62/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.62/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | k8_relset_1(X1,X2,X0,X2) = X1
% 7.62/1.49      | sK2 != X0
% 7.62/1.49      | k1_xboole_0 = X2 ),
% 7.62/1.49      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_497,plain,
% 7.62/1.49      ( ~ v1_funct_2(sK2,X0,X1)
% 7.62/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.62/1.49      | k8_relset_1(X0,X1,sK2,X1) = X0
% 7.62/1.49      | k1_xboole_0 = X1 ),
% 7.62/1.49      inference(unflattening,[status(thm)],[c_496]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_764,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 7.62/1.49      | X3 != X1
% 7.62/1.49      | X4 != X2
% 7.62/1.49      | k8_relset_1(X3,X4,sK2,X4) = X3
% 7.62/1.49      | k1_relset_1(X1,X2,X0) != X1
% 7.62/1.49      | sK2 != X0
% 7.62/1.49      | k1_xboole_0 = X2
% 7.62/1.49      | k1_xboole_0 = X4 ),
% 7.62/1.49      inference(resolution_lifted,[status(thm)],[c_21,c_497]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_765,plain,
% 7.62/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.62/1.49      | k8_relset_1(X0,X1,sK2,X1) = X0
% 7.62/1.49      | k1_relset_1(X0,X1,sK2) != X0
% 7.62/1.49      | k1_xboole_0 = X1 ),
% 7.62/1.49      inference(unflattening,[status(thm)],[c_764]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1957,plain,
% 7.62/1.49      ( k8_relset_1(X0,X1,sK2,X1) = X0
% 7.62/1.49      | k1_relset_1(X0,X1,sK2) != X0
% 7.62/1.49      | k1_xboole_0 = X1
% 7.62/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_765]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_4025,plain,
% 7.62/1.49      ( k8_relset_1(sK0,k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = sK0
% 7.62/1.49      | k1_relat_1(sK2) != sK0
% 7.62/1.49      | k2_relat_1(sK2) = k1_xboole_0
% 7.62/1.49      | sK1 = k1_xboole_0
% 7.62/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_3826,c_1957]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6,plain,
% 7.62/1.49      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.62/1.49      | k1_xboole_0 = X0
% 7.62/1.49      | k1_xboole_0 = X1 ),
% 7.62/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_101,plain,
% 7.62/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.62/1.49      | k1_xboole_0 = k1_xboole_0 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_5,plain,
% 7.62/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.62/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_102,plain,
% 7.62/1.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_9,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.62/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2371,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_relat_1(sK2)))
% 7.62/1.49      | r1_tarski(X0,k2_relat_1(sK2)) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2373,plain,
% 7.62/1.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_relat_1(sK2)))
% 7.62/1.49      | r1_tarski(k1_xboole_0,k2_relat_1(sK2)) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_2371]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1337,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2587,plain,
% 7.62/1.49      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_1337]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2588,plain,
% 7.62/1.49      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_2587]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2344,plain,
% 7.62/1.49      ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0))
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),X0) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2886,plain,
% 7.62/1.49      ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),sK1) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_2344]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_0,plain,
% 7.62/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.62/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3233,plain,
% 7.62/1.49      ( ~ r1_tarski(X0,k2_relat_1(sK2))
% 7.62/1.49      | ~ r1_tarski(k2_relat_1(sK2),X0)
% 7.62/1.49      | k2_relat_1(sK2) = X0 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3235,plain,
% 7.62/1.49      ( ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
% 7.62/1.49      | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
% 7.62/1.49      | k2_relat_1(sK2) = k1_xboole_0 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_3233]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1336,plain,( X0 = X0 ),theory(equality) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3239,plain,
% 7.62/1.49      ( k2_relat_1(sK2) = k2_relat_1(sK2) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_1336]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10,plain,
% 7.62/1.49      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 7.62/1.49      | ~ v1_relat_1(X1)
% 7.62/1.49      | ~ v1_funct_1(X1)
% 7.62/1.49      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 7.62/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_451,plain,
% 7.62/1.49      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 7.62/1.49      | ~ v1_relat_1(X1)
% 7.62/1.49      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
% 7.62/1.49      | sK2 != X1 ),
% 7.62/1.49      inference(resolution_lifted,[status(thm)],[c_10,c_33]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_452,plain,
% 7.62/1.49      ( ~ r1_tarski(X0,k2_relat_1(sK2))
% 7.62/1.49      | ~ v1_relat_1(sK2)
% 7.62/1.49      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
% 7.62/1.49      inference(unflattening,[status(thm)],[c_451]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1965,plain,
% 7.62/1.49      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 7.62/1.49      | r1_tarski(X0,k2_relat_1(sK2)) != iProver_top
% 7.62/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_453,plain,
% 7.62/1.49      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 7.62/1.49      | r1_tarski(X0,k2_relat_1(sK2)) != iProver_top
% 7.62/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2238,plain,
% 7.62/1.49      ( r1_tarski(X0,k2_relat_1(sK2)) != iProver_top
% 7.62/1.49      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_1965,c_36,c_453,c_2233]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2239,plain,
% 7.62/1.49      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 7.62/1.49      | r1_tarski(X0,k2_relat_1(sK2)) != iProver_top ),
% 7.62/1.49      inference(renaming,[status(thm)],[c_2238]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2429,plain,
% 7.62/1.49      ( k9_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2))) = k2_relat_1(sK2) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_1978,c_2239]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_14,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.62/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1970,plain,
% 7.62/1.49      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.62/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_4802,plain,
% 7.62/1.49      ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_1966,c_1970]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_12,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 7.62/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1972,plain,
% 7.62/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.62/1.49      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_4945,plain,
% 7.62/1.49      ( m1_subset_1(k9_relat_1(sK2,X0),k1_zfmisc_1(sK1)) = iProver_top
% 7.62/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_4802,c_1972]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_5202,plain,
% 7.62/1.49      ( m1_subset_1(k9_relat_1(sK2,X0),k1_zfmisc_1(sK1)) = iProver_top ),
% 7.62/1.49      inference(global_propositional_subsumption,[status(thm)],[c_4945,c_36]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_5210,plain,
% 7.62/1.49      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_2429,c_5202]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_5217,plain,
% 7.62/1.49      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
% 7.62/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_5210]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_7,plain,
% 7.62/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.62/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_5540,plain,
% 7.62/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_relat_1(sK2))) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1338,plain,
% 7.62/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.62/1.49      theory(equality) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2355,plain,
% 7.62/1.49      ( ~ r1_tarski(X0,X1)
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),X2)
% 7.62/1.49      | X2 != X1
% 7.62/1.49      | k2_relat_1(sK2) != X0 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_1338]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3238,plain,
% 7.62/1.49      ( ~ r1_tarski(k2_relat_1(sK2),X0)
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),X1)
% 7.62/1.49      | X1 != X0
% 7.62/1.49      | k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_2355]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_8293,plain,
% 7.62/1.49      ( r1_tarski(k2_relat_1(sK2),X0)
% 7.62/1.49      | ~ r1_tarski(k2_relat_1(sK2),sK1)
% 7.62/1.49      | X0 != sK1
% 7.62/1.49      | k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_3238]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_8299,plain,
% 7.62/1.49      ( ~ r1_tarski(k2_relat_1(sK2),sK1)
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),k1_xboole_0)
% 7.62/1.49      | k2_relat_1(sK2) != k2_relat_1(sK2)
% 7.62/1.49      | k1_xboole_0 != sK1 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_8293]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10312,plain,
% 7.62/1.49      ( k2_relat_1(sK2) = k1_xboole_0
% 7.62/1.49      | k8_relset_1(sK0,k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = sK0
% 7.62/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) != iProver_top ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_4025,c_101,c_102,c_2373,c_2588,c_2886,c_3235,c_3239,
% 7.62/1.49                 c_3750,c_5217,c_5540,c_8299]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10313,plain,
% 7.62/1.49      ( k8_relset_1(sK0,k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = sK0
% 7.62/1.49      | k2_relat_1(sK2) = k1_xboole_0
% 7.62/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) != iProver_top ),
% 7.62/1.49      inference(renaming,[status(thm)],[c_10312]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10320,plain,
% 7.62/1.49      ( k8_relset_1(sK0,k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = sK0
% 7.62/1.49      | k2_relat_1(sK2) = k1_xboole_0
% 7.62/1.49      | sK1 = k1_xboole_0
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_3829,c_10313]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2350,plain,
% 7.62/1.49      ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10336,plain,
% 7.62/1.49      ( ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
% 7.62/1.49      | k8_relset_1(sK0,k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = sK0
% 7.62/1.49      | k2_relat_1(sK2) = k1_xboole_0
% 7.62/1.49      | sK1 = k1_xboole_0 ),
% 7.62/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_10320]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10338,plain,
% 7.62/1.49      ( k8_relset_1(sK0,k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = sK0
% 7.62/1.49      | k2_relat_1(sK2) = k1_xboole_0 ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_10320,c_101,c_102,c_2350,c_2373,c_2588,c_2886,c_3235,
% 7.62/1.49                 c_3239,c_5217,c_5540,c_8299,c_10336]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_15,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 7.62/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1969,plain,
% 7.62/1.49      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 7.62/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_4270,plain,
% 7.62/1.49      ( k8_relset_1(k1_relat_1(sK2),X0,sK2,X1) = k10_relat_1(sK2,X1)
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_2292,c_1969]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_4443,plain,
% 7.62/1.49      ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_1978,c_4270]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6221,plain,
% 7.62/1.49      ( k8_relset_1(sK0,k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0)
% 7.62/1.49      | sK1 = k1_xboole_0 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_3750,c_4443]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10345,plain,
% 7.62/1.49      ( k10_relat_1(sK2,k2_relat_1(sK2)) = sK0
% 7.62/1.49      | k2_relat_1(sK2) = k1_xboole_0
% 7.62/1.49      | sK1 = k1_xboole_0 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_10338,c_6221]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10470,plain,
% 7.62/1.49      ( k2_relat_1(sK2) = k1_xboole_0
% 7.62/1.49      | k10_relat_1(sK2,k2_relat_1(sK2)) = sK0 ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_10345,c_101,c_102,c_2373,c_2588,c_2886,c_3235,c_3239,
% 7.62/1.49                 c_5217,c_5540,c_8299]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10471,plain,
% 7.62/1.49      ( k10_relat_1(sK2,k2_relat_1(sK2)) = sK0
% 7.62/1.49      | k2_relat_1(sK2) = k1_xboole_0 ),
% 7.62/1.49      inference(renaming,[status(thm)],[c_10470]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10474,plain,
% 7.62/1.49      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) | k2_relat_1(sK2) = k1_xboole_0 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_10471,c_2429]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_4269,plain,
% 7.62/1.49      ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_1966,c_1969]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_29,negated_conjecture,
% 7.62/1.49      ( k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) != sK0 ),
% 7.62/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_4359,plain,
% 7.62/1.49      ( k10_relat_1(sK2,k7_relset_1(sK0,sK1,sK2,sK0)) != sK0 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_4269,c_29]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_4944,plain,
% 7.62/1.49      ( k10_relat_1(sK2,k9_relat_1(sK2,sK0)) != sK0 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_4802,c_4359]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10482,plain,
% 7.62/1.49      ( k10_relat_1(sK2,k2_relat_1(sK2)) != sK0
% 7.62/1.49      | k2_relat_1(sK2) = k1_xboole_0 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_10474,c_4944]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10617,plain,
% 7.62/1.49      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_10482,c_10471]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10678,plain,
% 7.62/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top
% 7.62/1.49      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_10617,c_2292]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_98,plain,
% 7.62/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2345,plain,
% 7.62/1.49      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0)) != iProver_top
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),X0) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_2344]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2464,plain,
% 7.62/1.49      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_1336]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1341,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.62/1.49      theory(equality) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2273,plain,
% 7.62/1.49      ( m1_subset_1(X0,X1)
% 7.62/1.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
% 7.62/1.49      | X1 != k1_zfmisc_1(X2)
% 7.62/1.49      | X0 != k1_xboole_0 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_1341]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2463,plain,
% 7.62/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.62/1.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
% 7.62/1.49      | X0 != k1_xboole_0
% 7.62/1.49      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_2273]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3121,plain,
% 7.62/1.49      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0))
% 7.62/1.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
% 7.62/1.49      | k2_relat_1(sK2) != k1_xboole_0
% 7.62/1.49      | k1_zfmisc_1(X0) != k1_zfmisc_1(X0) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_2463]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3127,plain,
% 7.62/1.49      ( k2_relat_1(sK2) != k1_xboole_0
% 7.62/1.49      | k1_zfmisc_1(X0) != k1_zfmisc_1(X0)
% 7.62/1.49      | m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0)) = iProver_top
% 7.62/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_3121]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_11184,plain,
% 7.62/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_10678,c_36,c_98,c_483,c_2233,c_2345,c_2464,c_3127,c_10471,
% 7.62/1.49                 c_10482]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_11192,plain,
% 7.62/1.49      ( sK1 = k1_xboole_0
% 7.62/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_3750,c_11184]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_16,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1968,plain,
% 7.62/1.49      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 7.62/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_11242,plain,
% 7.62/1.49      ( k8_relset_1(sK0,X0,sK2,X0) = k1_relset_1(sK0,X0,sK2)
% 7.62/1.49      | sK1 = k1_xboole_0 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_11192,c_1968]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_4,plain,
% 7.62/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.62/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1974,plain,
% 7.62/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.62/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2970,plain,
% 7.62/1.49      ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 7.62/1.49      | r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),X0)) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_2292,c_1974]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1979,plain,
% 7.62/1.49      ( X0 = X1
% 7.62/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.62/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_4236,plain,
% 7.62/1.49      ( k2_zfmisc_1(k1_relat_1(sK2),X0) = sK2
% 7.62/1.49      | r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),X0),sK2) != iProver_top
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_2970,c_1979]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_8324,plain,
% 7.62/1.49      ( k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0) = sK2
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top
% 7.62/1.49      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_4,c_4236]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_8337,plain,
% 7.62/1.49      ( sK2 = k1_xboole_0
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top
% 7.62/1.49      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_8324,c_4]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3994,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) | r1_tarski(X0,sK2) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3995,plain,
% 7.62/1.49      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 7.62/1.49      | r1_tarski(X0,sK2) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_3994]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3997,plain,
% 7.62/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) != iProver_top
% 7.62/1.49      | r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_3995]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6732,plain,
% 7.62/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6735,plain,
% 7.62/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_6732]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_8757,plain,
% 7.62/1.49      ( r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top
% 7.62/1.49      | sK2 = k1_xboole_0 ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_8337,c_3997,c_6735]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_8758,plain,
% 7.62/1.49      ( sK2 = k1_xboole_0
% 7.62/1.49      | r1_tarski(k2_relat_1(sK2),k1_xboole_0) != iProver_top ),
% 7.62/1.49      inference(renaming,[status(thm)],[c_8757]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10639,plain,
% 7.62/1.49      ( sK2 = k1_xboole_0 | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_10617,c_8758]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_93,plain,
% 7.62/1.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 7.62/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_99,plain,
% 7.62/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2357,plain,
% 7.62/1.49      ( r1_tarski(k2_relat_1(sK2),k1_xboole_0)
% 7.62/1.49      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.62/1.49      | k2_relat_1(sK2) != k1_xboole_0
% 7.62/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_2355]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3996,plain,
% 7.62/1.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
% 7.62/1.49      | r1_tarski(k1_xboole_0,sK2) ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_3994]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_8344,plain,
% 7.62/1.49      ( ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
% 7.62/1.49      | ~ r1_tarski(k1_xboole_0,sK2)
% 7.62/1.49      | sK2 = k1_xboole_0 ),
% 7.62/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_8337]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_12372,plain,
% 7.62/1.49      ( sK2 = k1_xboole_0 ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_10639,c_93,c_99,c_101,c_102,c_2357,c_3996,c_6732,c_8344,
% 7.62/1.49                 c_10471,c_10482]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_17048,plain,
% 7.62/1.49      ( k8_relset_1(sK0,X0,k1_xboole_0,X0) = k1_relset_1(sK0,X0,k1_xboole_0)
% 7.62/1.49      | sK1 = k1_xboole_0 ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_11242,c_12372]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_12409,plain,
% 7.62/1.49      ( k1_relset_1(sK0,sK1,k1_xboole_0) = sK0 | sK1 = k1_xboole_0 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_12372,c_732]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1976,plain,
% 7.62/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3645,plain,
% 7.62/1.49      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_1976,c_1971]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_12414,plain,
% 7.62/1.49      ( k1_relat_1(k1_xboole_0) = sK0 | sK1 = k1_xboole_0 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_12409,c_3645]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_100,plain,
% 7.62/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_98]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_19,plain,
% 7.62/1.49      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.62/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.62/1.49      | k1_xboole_0 = X1
% 7.62/1.49      | k1_xboole_0 = X0 ),
% 7.62/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_620,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.62/1.49      | sK2 != X0
% 7.62/1.49      | sK1 != k1_xboole_0
% 7.62/1.49      | sK0 != X1
% 7.62/1.49      | k1_xboole_0 = X0
% 7.62/1.49      | k1_xboole_0 = X1 ),
% 7.62/1.49      inference(resolution_lifted,[status(thm)],[c_19,c_32]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_621,plain,
% 7.62/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 7.62/1.49      | sK1 != k1_xboole_0
% 7.62/1.49      | k1_xboole_0 = sK2
% 7.62/1.49      | k1_xboole_0 = sK0 ),
% 7.62/1.49      inference(unflattening,[status(thm)],[c_620]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1963,plain,
% 7.62/1.49      ( sK1 != k1_xboole_0
% 7.62/1.49      | k1_xboole_0 = sK2
% 7.62/1.49      | k1_xboole_0 = sK0
% 7.62/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_621]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2084,plain,
% 7.62/1.49      ( sK2 = k1_xboole_0
% 7.62/1.49      | sK1 != k1_xboole_0
% 7.62/1.49      | sK0 = k1_xboole_0
% 7.62/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_1963,c_4]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_30,negated_conjecture,
% 7.62/1.49      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 7.62/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2257,plain,
% 7.62/1.49      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_1337]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2394,plain,
% 7.62/1.49      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_2257]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2395,plain,
% 7.62/1.49      ( sK0 = sK0 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_1336]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2590,plain,
% 7.62/1.49      ( sK0 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_2084,c_30,c_101,c_102,c_2394,c_2395,c_2588]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2591,plain,
% 7.62/1.49      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 7.62/1.49      inference(renaming,[status(thm)],[c_2590]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3341,plain,
% 7.62/1.49      ( X0 != X1 | X0 = sK0 | sK0 != X1 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_1337]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_7100,plain,
% 7.62/1.49      ( k1_relat_1(X0) != X1 | k1_relat_1(X0) = sK0 | sK0 != X1 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_3341]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_7106,plain,
% 7.62/1.49      ( k1_relat_1(k1_xboole_0) = sK0
% 7.62/1.49      | k1_relat_1(k1_xboole_0) != k1_xboole_0
% 7.62/1.49      | sK0 != k1_xboole_0 ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_7100]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_22,plain,
% 7.62/1.49      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.62/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.62/1.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.62/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_660,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.62/1.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 7.62/1.49      | sK2 != X0
% 7.62/1.49      | sK1 != X1
% 7.62/1.49      | sK0 != k1_xboole_0 ),
% 7.62/1.49      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_661,plain,
% 7.62/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 7.62/1.49      | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 7.62/1.49      | sK0 != k1_xboole_0 ),
% 7.62/1.49      inference(unflattening,[status(thm)],[c_660]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1961,plain,
% 7.62/1.49      ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 7.62/1.49      | sK0 != k1_xboole_0
% 7.62/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2056,plain,
% 7.62/1.49      ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 7.62/1.49      | sK0 != k1_xboole_0
% 7.62/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_1961,c_5]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_12407,plain,
% 7.62/1.49      ( k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) = k1_xboole_0
% 7.62/1.49      | sK0 != k1_xboole_0
% 7.62/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_12372,c_2056]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_12424,plain,
% 7.62/1.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 7.62/1.49      | sK0 != k1_xboole_0
% 7.62/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_12407,c_3645]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_13399,plain,
% 7.62/1.49      ( k1_relat_1(k1_xboole_0) = sK0 ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_12414,c_100,c_2591,c_7106,c_12424]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_13402,plain,
% 7.62/1.49      ( k1_relset_1(X0,X1,k1_xboole_0) = sK0 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_13399,c_3645]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_11197,plain,
% 7.62/1.49      ( k8_relset_1(k1_relat_1(sK2),X0,sK2,X1) = k10_relat_1(sK2,X1) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_11184,c_1969]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_14946,plain,
% 7.62/1.49      ( k8_relset_1(sK0,X0,k1_xboole_0,X1) = k10_relat_1(k1_xboole_0,X1) ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_11197,c_12372,c_13399]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_17049,plain,
% 7.62/1.49      ( k10_relat_1(k1_xboole_0,X0) = sK0 | sK1 = k1_xboole_0 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_17048,c_13402,c_14946]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_12394,plain,
% 7.62/1.49      ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,sK0)) != sK0 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_12372,c_4944]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_17054,plain,
% 7.62/1.49      ( sK1 = k1_xboole_0 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_17049,c_12394]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6609,plain,
% 7.62/1.49      ( k8_relset_1(sK0,sK1,sK2,sK1) = k1_relset_1(sK0,sK1,sK2) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_1966,c_1968]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6633,plain,
% 7.62/1.49      ( k8_relset_1(sK0,sK1,sK2,sK1) = k1_relat_1(sK2) ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_6609,c_3648]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6849,plain,
% 7.62/1.49      ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_6633,c_4269]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_12388,plain,
% 7.62/1.49      ( k10_relat_1(k1_xboole_0,sK1) = k1_relat_1(k1_xboole_0) ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_12372,c_6849]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_13497,plain,
% 7.62/1.49      ( k10_relat_1(k1_xboole_0,sK1) = sK0 ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_12388,c_13399]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_17173,plain,
% 7.62/1.49      ( k10_relat_1(k1_xboole_0,k1_xboole_0) = sK0 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_17054,c_13497]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_17176,plain,
% 7.62/1.49      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_17054,c_2591]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_17178,plain,
% 7.62/1.49      ( sK0 = k1_xboole_0 ),
% 7.62/1.49      inference(equality_resolution_simp,[status(thm)],[c_17176]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_17181,plain,
% 7.62/1.49      ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_17173,c_17178]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2967,plain,
% 7.62/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_1976,c_1974]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_4688,plain,
% 7.62/1.49      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_2967,c_2239]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_12393,plain,
% 7.62/1.49      ( k9_relat_1(k1_xboole_0,k10_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_12372,c_4688]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_26375,plain,
% 7.62/1.49      ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_17181,c_12393]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_17792,plain,
% 7.62/1.49      ( k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_17178,c_12394]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_26379,plain,
% 7.62/1.49      ( k10_relat_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_26375,c_17792]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_26381,plain,
% 7.62/1.49      ( k1_xboole_0 != k1_xboole_0 ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_26379,c_17181]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_26382,plain,
% 7.62/1.49      ( $false ),
% 7.62/1.49      inference(equality_resolution_simp,[status(thm)],[c_26381]) ).
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  ------                               Statistics
% 7.62/1.49  
% 7.62/1.49  ------ General
% 7.62/1.49  
% 7.62/1.49  abstr_ref_over_cycles:                  0
% 7.62/1.49  abstr_ref_under_cycles:                 0
% 7.62/1.49  gc_basic_clause_elim:                   0
% 7.62/1.49  forced_gc_time:                         0
% 7.62/1.49  parsing_time:                           0.01
% 7.62/1.49  unif_index_cands_time:                  0.
% 7.62/1.49  unif_index_add_time:                    0.
% 7.62/1.49  orderings_time:                         0.
% 7.62/1.49  out_proof_time:                         0.015
% 7.62/1.49  total_time:                             0.671
% 7.62/1.49  num_of_symbols:                         50
% 7.62/1.49  num_of_terms:                           19676
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing
% 7.62/1.49  
% 7.62/1.49  num_of_splits:                          0
% 7.62/1.49  num_of_split_atoms:                     0
% 7.62/1.49  num_of_reused_defs:                     0
% 7.62/1.49  num_eq_ax_congr_red:                    19
% 7.62/1.49  num_of_sem_filtered_clauses:            1
% 7.62/1.49  num_of_subtypes:                        0
% 7.62/1.49  monotx_restored_types:                  0
% 7.62/1.49  sat_num_of_epr_types:                   0
% 7.62/1.49  sat_num_of_non_cyclic_types:            0
% 7.62/1.49  sat_guarded_non_collapsed_types:        0
% 7.62/1.49  num_pure_diseq_elim:                    0
% 7.62/1.49  simp_replaced_by:                       0
% 7.62/1.49  res_preprocessed:                       160
% 7.62/1.49  prep_upred:                             0
% 7.62/1.49  prep_unflattend:                        75
% 7.62/1.49  smt_new_axioms:                         0
% 7.62/1.49  pred_elim_cands:                        3
% 7.62/1.49  pred_elim:                              2
% 7.62/1.49  pred_elim_cl:                           -1
% 7.62/1.49  pred_elim_cycles:                       6
% 7.62/1.49  merged_defs:                            8
% 7.62/1.49  merged_defs_ncl:                        0
% 7.62/1.49  bin_hyper_res:                          8
% 7.62/1.49  prep_cycles:                            4
% 7.62/1.49  pred_elim_time:                         0.015
% 7.62/1.49  splitting_time:                         0.
% 7.62/1.49  sem_filter_time:                        0.
% 7.62/1.49  monotx_time:                            0.
% 7.62/1.49  subtype_inf_time:                       0.
% 7.62/1.49  
% 7.62/1.49  ------ Problem properties
% 7.62/1.49  
% 7.62/1.49  clauses:                                33
% 7.62/1.49  conjectures:                            3
% 7.62/1.49  epr:                                    4
% 7.62/1.49  horn:                                   25
% 7.62/1.49  ground:                                 9
% 7.62/1.49  unary:                                  6
% 7.62/1.49  binary:                                 13
% 7.62/1.49  lits:                                   81
% 7.62/1.49  lits_eq:                                42
% 7.62/1.49  fd_pure:                                0
% 7.62/1.49  fd_pseudo:                              0
% 7.62/1.49  fd_cond:                                4
% 7.62/1.49  fd_pseudo_cond:                         1
% 7.62/1.49  ac_symbols:                             0
% 7.62/1.49  
% 7.62/1.49  ------ Propositional Solver
% 7.62/1.49  
% 7.62/1.49  prop_solver_calls:                      30
% 7.62/1.49  prop_fast_solver_calls:                 1740
% 7.62/1.49  smt_solver_calls:                       0
% 7.62/1.49  smt_fast_solver_calls:                  0
% 7.62/1.49  prop_num_of_clauses:                    9527
% 7.62/1.49  prop_preprocess_simplified:             18839
% 7.62/1.49  prop_fo_subsumed:                       68
% 7.62/1.49  prop_solver_time:                       0.
% 7.62/1.49  smt_solver_time:                        0.
% 7.62/1.49  smt_fast_solver_time:                   0.
% 7.62/1.49  prop_fast_solver_time:                  0.
% 7.62/1.49  prop_unsat_core_time:                   0.
% 7.62/1.49  
% 7.62/1.49  ------ QBF
% 7.62/1.49  
% 7.62/1.49  qbf_q_res:                              0
% 7.62/1.49  qbf_num_tautologies:                    0
% 7.62/1.49  qbf_prep_cycles:                        0
% 7.62/1.49  
% 7.62/1.49  ------ BMC1
% 7.62/1.49  
% 7.62/1.49  bmc1_current_bound:                     -1
% 7.62/1.49  bmc1_last_solved_bound:                 -1
% 7.62/1.49  bmc1_unsat_core_size:                   -1
% 7.62/1.49  bmc1_unsat_core_parents_size:           -1
% 7.62/1.49  bmc1_merge_next_fun:                    0
% 7.62/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.62/1.49  
% 7.62/1.49  ------ Instantiation
% 7.62/1.49  
% 7.62/1.49  inst_num_of_clauses:                    2878
% 7.62/1.49  inst_num_in_passive:                    578
% 7.62/1.49  inst_num_in_active:                     1109
% 7.62/1.49  inst_num_in_unprocessed:                1193
% 7.62/1.49  inst_num_of_loops:                      1490
% 7.62/1.49  inst_num_of_learning_restarts:          0
% 7.62/1.49  inst_num_moves_active_passive:          378
% 7.62/1.49  inst_lit_activity:                      0
% 7.62/1.49  inst_lit_activity_moves:                0
% 7.62/1.49  inst_num_tautologies:                   0
% 7.62/1.49  inst_num_prop_implied:                  0
% 7.62/1.49  inst_num_existing_simplified:           0
% 7.62/1.49  inst_num_eq_res_simplified:             0
% 7.62/1.49  inst_num_child_elim:                    0
% 7.62/1.49  inst_num_of_dismatching_blockings:      1305
% 7.62/1.49  inst_num_of_non_proper_insts:           3570
% 7.62/1.49  inst_num_of_duplicates:                 0
% 7.62/1.49  inst_inst_num_from_inst_to_res:         0
% 7.62/1.49  inst_dismatching_checking_time:         0.
% 7.62/1.49  
% 7.62/1.49  ------ Resolution
% 7.62/1.49  
% 7.62/1.49  res_num_of_clauses:                     0
% 7.62/1.49  res_num_in_passive:                     0
% 7.62/1.49  res_num_in_active:                      0
% 7.62/1.49  res_num_of_loops:                       164
% 7.62/1.49  res_forward_subset_subsumed:            170
% 7.62/1.49  res_backward_subset_subsumed:           5
% 7.62/1.49  res_forward_subsumed:                   0
% 7.62/1.49  res_backward_subsumed:                  0
% 7.62/1.49  res_forward_subsumption_resolution:     1
% 7.62/1.49  res_backward_subsumption_resolution:    0
% 7.62/1.49  res_clause_to_clause_subsumption:       2869
% 7.62/1.49  res_orphan_elimination:                 0
% 7.62/1.49  res_tautology_del:                      198
% 7.62/1.49  res_num_eq_res_simplified:              0
% 7.62/1.49  res_num_sel_changes:                    0
% 7.62/1.49  res_moves_from_active_to_pass:          0
% 7.62/1.49  
% 7.62/1.49  ------ Superposition
% 7.62/1.49  
% 7.62/1.49  sup_time_total:                         0.
% 7.62/1.49  sup_time_generating:                    0.
% 7.62/1.49  sup_time_sim_full:                      0.
% 7.62/1.49  sup_time_sim_immed:                     0.
% 7.62/1.49  
% 7.62/1.49  sup_num_of_clauses:                     590
% 7.62/1.49  sup_num_in_active:                      160
% 7.62/1.49  sup_num_in_passive:                     430
% 7.62/1.49  sup_num_of_loops:                       297
% 7.62/1.49  sup_fw_superposition:                   713
% 7.62/1.49  sup_bw_superposition:                   734
% 7.62/1.49  sup_immediate_simplified:               544
% 7.62/1.49  sup_given_eliminated:                   4
% 7.62/1.49  comparisons_done:                       0
% 7.62/1.49  comparisons_avoided:                    83
% 7.62/1.49  
% 7.62/1.49  ------ Simplifications
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  sim_fw_subset_subsumed:                 35
% 7.62/1.49  sim_bw_subset_subsumed:                 34
% 7.62/1.49  sim_fw_subsumed:                        43
% 7.62/1.49  sim_bw_subsumed:                        15
% 7.62/1.49  sim_fw_subsumption_res:                 3
% 7.62/1.49  sim_bw_subsumption_res:                 0
% 7.62/1.49  sim_tautology_del:                      4
% 7.62/1.49  sim_eq_tautology_del:                   26
% 7.62/1.49  sim_eq_res_simp:                        1
% 7.62/1.49  sim_fw_demodulated:                     195
% 7.62/1.49  sim_bw_demodulated:                     328
% 7.62/1.49  sim_light_normalised:                   176
% 7.62/1.49  sim_joinable_taut:                      0
% 7.62/1.49  sim_joinable_simp:                      0
% 7.62/1.49  sim_ac_normalised:                      0
% 7.62/1.49  sim_smt_subsumption:                    0
% 7.62/1.49  
%------------------------------------------------------------------------------
