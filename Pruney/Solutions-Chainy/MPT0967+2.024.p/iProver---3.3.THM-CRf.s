%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:42 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :  255 (5515 expanded)
%              Number of clauses        :  183 (2060 expanded)
%              Number of leaves         :   20 (1085 expanded)
%              Depth                    :   31
%              Number of atoms          :  687 (25532 expanded)
%              Number of equality atoms :  356 (5711 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f42,plain,
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

fof(f43,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f42])).

fof(f73,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
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
    inference(nnf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f52])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_32])).

cnf(c_528,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_530,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_528,c_31])).

cnf(c_1333,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1336,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2638,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1333,c_1336])).

cnf(c_2733,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_530,c_2638])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_14])).

cnf(c_1331,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_2388,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1333,c_1331])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_238,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_239,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_238])).

cnf(c_298,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_239])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1899,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[status(thm)],[c_11,c_31])).

cnf(c_2290,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_298,c_1899])).

cnf(c_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2425,plain,
    ( v1_relat_1(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2290,c_17])).

cnf(c_2426,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2425])).

cnf(c_2736,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2388,c_2426])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1343,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3779,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2736,c_1343])).

cnf(c_1339,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2514,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_1331])).

cnf(c_6275,plain,
    ( r1_tarski(k1_relat_1(k1_relat_1(sK3)),X0) = iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3779,c_2514])).

cnf(c_69,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1332,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_3470,plain,
    ( v1_relat_1(k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2736,c_1332])).

cnf(c_1586,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_7730,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_1586])).

cnf(c_7736,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7730])).

cnf(c_22798,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(X0,X1)) != iProver_top
    | r1_tarski(k1_relat_1(k1_relat_1(sK3)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6275,c_69,c_3470,c_7736])).

cnf(c_22799,plain,
    ( r1_tarski(k1_relat_1(k1_relat_1(sK3)),X0) = iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_22798])).

cnf(c_22808,plain,
    ( r1_tarski(k1_relat_1(k1_relat_1(sK3)),X0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_22799])).

cnf(c_30,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1334,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_16,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_16])).

cnf(c_1330,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_415])).

cnf(c_1807,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1333,c_1330])).

cnf(c_3778,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1807,c_1343])).

cnf(c_4902,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3778,c_2426])).

cnf(c_4903,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4902])).

cnf(c_4910,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X1) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4903,c_1343])).

cnf(c_10717,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1334,c_4910])).

cnf(c_8310,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_415,c_31])).

cnf(c_1808,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1807])).

cnf(c_8694,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8310,c_1808,c_2425])).

cnf(c_2541,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(X0,sK2) ),
    inference(resolution,[status(thm)],[c_3,c_30])).

cnf(c_8718,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(resolution,[status(thm)],[c_8694,c_2541])).

cnf(c_8719,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8718])).

cnf(c_11653,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10717,c_8719])).

cnf(c_11660,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11653,c_1343])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1345,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_12367,plain,
    ( k2_relat_1(sK3) = X0
    | r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11660,c_1345])).

cnf(c_37,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1603,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_tarski(sK2,sK1)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1604,plain,
    ( sK1 = sK2
    | r1_tarski(sK1,sK2) != iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1603])).

cnf(c_1775,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1776,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1775])).

cnf(c_2414,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2388])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_28,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_171,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_33])).

cnf(c_172,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(renaming,[status(thm)],[c_171])).

cnf(c_538,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | sK1 != sK2
    | sK0 != sK0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_172,c_32])).

cnf(c_605,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | sK1 != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_538])).

cnf(c_4526,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | sK1 != sK2 ),
    inference(resolution,[status(thm)],[c_21,c_605])).

cnf(c_8716,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK3))
    | r1_tarski(X0,sK1) ),
    inference(resolution,[status(thm)],[c_8694,c_3])).

cnf(c_8717,plain,
    ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
    | r1_tarski(X0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8716])).

cnf(c_14855,plain,
    ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12367,c_37,c_1604,c_1776,c_2414,c_2425,c_4526,c_8717,c_8718])).

cnf(c_23346,plain,
    ( r1_tarski(sK2,k1_relat_1(k1_relat_1(sK3))) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22808,c_14855])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1639,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_785,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1745,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_787,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1698,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_1931,plain,
    ( ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != sK0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1698])).

cnf(c_2335,plain,
    ( ~ r1_tarski(sK0,sK0)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != sK0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1931])).

cnf(c_2337,plain,
    ( sK0 != sK0
    | k1_xboole_0 != sK0
    | r1_tarski(sK0,sK0) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2335])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2336,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2339,plain,
    ( r1_tarski(sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2336])).

cnf(c_786,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2677,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_786,c_785])).

cnf(c_5576,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[status(thm)],[c_2677,c_530])).

cnf(c_6114,plain,
    ( X0 != X1
    | X0 = k1_relset_1(sK0,sK1,sK3)
    | k1_relset_1(sK0,sK1,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_9228,plain,
    ( X0 = k1_relset_1(sK0,sK1,sK3)
    | X0 != k1_relat_1(sK3)
    | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6114])).

cnf(c_14613,plain,
    ( k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9228])).

cnf(c_14614,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_3651,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 != k1_relat_1(X0)
    | k1_relset_1(X1,X2,X0) = X3 ),
    inference(resolution,[status(thm)],[c_20,c_786])).

cnf(c_25,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_172])).

cnf(c_515,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_14508,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | sK0 != k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[status(thm)],[c_3651,c_515])).

cnf(c_1777,plain,
    ( r1_tarski(sK2,sK1)
    | ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_1775])).

cnf(c_2235,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_2090,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_2234,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_2090])).

cnf(c_3445,plain,
    ( ~ r1_tarski(sK2,sK2)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2234])).

cnf(c_3446,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_7042,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_14635,plain,
    ( sK0 != k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14508,c_30,c_1603,c_1777,c_2235,c_2414,c_2425,c_3445,c_3446,c_4526,c_7042,c_8718])).

cnf(c_14636,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | sK0 != k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_14635])).

cnf(c_14653,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | sK0 != k1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_14636,c_21])).

cnf(c_1746,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_3426,plain,
    ( X0 != k1_relset_1(sK0,sK1,sK3)
    | sK0 = X0
    | sK0 != k1_relset_1(sK0,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_1746])).

cnf(c_32838,plain,
    ( k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3)
    | sK0 != k1_relset_1(sK0,sK1,sK3)
    | sK0 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3426])).

cnf(c_33273,plain,
    ( r1_tarski(sK2,k1_relat_1(k1_relat_1(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23346,c_31,c_29,c_1639,c_1745,c_2337,c_2339,c_2414,c_2425,c_5576,c_8718,c_14613,c_14614,c_14653,c_32838])).

cnf(c_33278,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2733,c_33273])).

cnf(c_1612,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_1738,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1612])).

cnf(c_1739,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_34245,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_33278,c_31,c_1639,c_1738,c_1739,c_2414,c_2425,c_5576,c_8718,c_14613,c_14614,c_14653,c_32838])).

cnf(c_1338,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2506,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1333,c_1338])).

cnf(c_34333,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_34245,c_2506])).

cnf(c_34341,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_34245,c_29])).

cnf(c_34342,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_34341])).

cnf(c_34367,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34333,c_34342])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_34369,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_34367,c_7])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1341,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_35292,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_34369,c_1341])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != X1
    | sK0 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_172])).

cnf(c_486,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_1327,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_1464,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1327,c_7])).

cnf(c_34716,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_34342,c_1464])).

cnf(c_34726,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_34716])).

cnf(c_34730,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_34726,c_7])).

cnf(c_1687,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_1924,plain,
    ( ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != sK1
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1687])).

cnf(c_2323,plain,
    ( ~ r1_tarski(sK1,sK1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != sK1
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1924])).

cnf(c_2325,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK1
    | r1_tarski(sK1,sK1) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2323])).

cnf(c_2324,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2327,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2324])).

cnf(c_1335,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4346,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1335])).

cnf(c_4633,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2736,c_4346])).

cnf(c_5015,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4633,c_2426])).

cnf(c_5016,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5015])).

cnf(c_5021,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4903,c_5016])).

cnf(c_35725,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_34730,c_31,c_1639,c_1739,c_2325,c_2327,c_2414,c_2425,c_5021,c_5576,c_8718,c_14613,c_14614,c_14653,c_32838])).

cnf(c_35883,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_35292,c_35725])).

cnf(c_1344,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2637,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_1336])).

cnf(c_9254,plain,
    ( k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1344,c_2637])).

cnf(c_9310,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_9254])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1340,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2387,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1340,c_1331])).

cnf(c_71,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_1587,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1586])).

cnf(c_1589,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_1629,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1632,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1629])).

cnf(c_1634,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1632])).

cnf(c_1953,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1954,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1953])).

cnf(c_1956,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1954])).

cnf(c_5127,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2387,c_71,c_1589,c_1634,c_1956])).

cnf(c_5137,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5127,c_1341])).

cnf(c_9312,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9310,c_7,c_5137])).

cnf(c_35947,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_35883,c_9312])).

cnf(c_35948,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_35947])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:07:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.94/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.94/1.49  
% 7.94/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.94/1.49  
% 7.94/1.49  ------  iProver source info
% 7.94/1.49  
% 7.94/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.94/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.94/1.49  git: non_committed_changes: false
% 7.94/1.49  git: last_make_outside_of_git: false
% 7.94/1.49  
% 7.94/1.49  ------ 
% 7.94/1.49  ------ Parsing...
% 7.94/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.94/1.49  
% 7.94/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.94/1.49  
% 7.94/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.94/1.49  
% 7.94/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.49  ------ Proving...
% 7.94/1.49  ------ Problem Properties 
% 7.94/1.49  
% 7.94/1.49  
% 7.94/1.49  clauses                                 27
% 7.94/1.49  conjectures                             3
% 7.94/1.49  EPR                                     8
% 7.94/1.49  Horn                                    24
% 7.94/1.49  unary                                   8
% 7.94/1.49  binary                                  7
% 7.94/1.49  lits                                    62
% 7.94/1.49  lits eq                                 25
% 7.94/1.49  fd_pure                                 0
% 7.94/1.49  fd_pseudo                               0
% 7.94/1.49  fd_cond                                 2
% 7.94/1.49  fd_pseudo_cond                          1
% 7.94/1.49  AC symbols                              0
% 7.94/1.49  
% 7.94/1.49  ------ Input Options Time Limit: Unbounded
% 7.94/1.49  
% 7.94/1.49  
% 7.94/1.49  ------ 
% 7.94/1.49  Current options:
% 7.94/1.49  ------ 
% 7.94/1.49  
% 7.94/1.49  
% 7.94/1.49  
% 7.94/1.49  
% 7.94/1.49  ------ Proving...
% 7.94/1.49  
% 7.94/1.49  
% 7.94/1.49  % SZS status Theorem for theBenchmark.p
% 7.94/1.49  
% 7.94/1.49   Resolution empty clause
% 7.94/1.49  
% 7.94/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.94/1.49  
% 7.94/1.49  fof(f16,axiom,(
% 7.94/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.94/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f30,plain,(
% 7.94/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.94/1.49    inference(ennf_transformation,[],[f16])).
% 7.94/1.49  
% 7.94/1.49  fof(f31,plain,(
% 7.94/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.94/1.49    inference(flattening,[],[f30])).
% 7.94/1.49  
% 7.94/1.49  fof(f41,plain,(
% 7.94/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.94/1.49    inference(nnf_transformation,[],[f31])).
% 7.94/1.49  
% 7.94/1.49  fof(f66,plain,(
% 7.94/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.94/1.49    inference(cnf_transformation,[],[f41])).
% 7.94/1.49  
% 7.94/1.49  fof(f17,conjecture,(
% 7.94/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.94/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f18,negated_conjecture,(
% 7.94/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.94/1.49    inference(negated_conjecture,[],[f17])).
% 7.94/1.49  
% 7.94/1.49  fof(f32,plain,(
% 7.94/1.49    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.94/1.49    inference(ennf_transformation,[],[f18])).
% 7.94/1.49  
% 7.94/1.49  fof(f33,plain,(
% 7.94/1.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.94/1.49    inference(flattening,[],[f32])).
% 7.94/1.49  
% 7.94/1.49  fof(f42,plain,(
% 7.94/1.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 7.94/1.49    introduced(choice_axiom,[])).
% 7.94/1.49  
% 7.94/1.49  fof(f43,plain,(
% 7.94/1.49    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 7.94/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f42])).
% 7.94/1.49  
% 7.94/1.49  fof(f73,plain,(
% 7.94/1.49    v1_funct_2(sK3,sK0,sK1)),
% 7.94/1.49    inference(cnf_transformation,[],[f43])).
% 7.94/1.49  
% 7.94/1.49  fof(f74,plain,(
% 7.94/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.94/1.49    inference(cnf_transformation,[],[f43])).
% 7.94/1.49  
% 7.94/1.49  fof(f14,axiom,(
% 7.94/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.94/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f27,plain,(
% 7.94/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.94/1.49    inference(ennf_transformation,[],[f14])).
% 7.94/1.49  
% 7.94/1.49  fof(f64,plain,(
% 7.94/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.94/1.49    inference(cnf_transformation,[],[f27])).
% 7.94/1.49  
% 7.94/1.49  fof(f5,axiom,(
% 7.94/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.94/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f36,plain,(
% 7.94/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.94/1.49    inference(nnf_transformation,[],[f5])).
% 7.94/1.49  
% 7.94/1.49  fof(f37,plain,(
% 7.94/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.94/1.49    inference(flattening,[],[f36])).
% 7.94/1.49  
% 7.94/1.49  fof(f52,plain,(
% 7.94/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.94/1.49    inference(cnf_transformation,[],[f37])).
% 7.94/1.49  
% 7.94/1.49  fof(f80,plain,(
% 7.94/1.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.94/1.49    inference(equality_resolution,[],[f52])).
% 7.94/1.49  
% 7.94/1.49  fof(f13,axiom,(
% 7.94/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.94/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f26,plain,(
% 7.94/1.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.94/1.49    inference(ennf_transformation,[],[f13])).
% 7.94/1.49  
% 7.94/1.49  fof(f62,plain,(
% 7.94/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.94/1.49    inference(cnf_transformation,[],[f26])).
% 7.94/1.49  
% 7.94/1.49  fof(f10,axiom,(
% 7.94/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.94/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f24,plain,(
% 7.94/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.94/1.49    inference(ennf_transformation,[],[f10])).
% 7.94/1.49  
% 7.94/1.49  fof(f39,plain,(
% 7.94/1.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.94/1.49    inference(nnf_transformation,[],[f24])).
% 7.94/1.49  
% 7.94/1.49  fof(f57,plain,(
% 7.94/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.94/1.49    inference(cnf_transformation,[],[f39])).
% 7.94/1.49  
% 7.94/1.49  fof(f9,axiom,(
% 7.94/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.94/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f23,plain,(
% 7.94/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.94/1.49    inference(ennf_transformation,[],[f9])).
% 7.94/1.49  
% 7.94/1.49  fof(f56,plain,(
% 7.94/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.94/1.49    inference(cnf_transformation,[],[f23])).
% 7.94/1.49  
% 7.94/1.49  fof(f7,axiom,(
% 7.94/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.94/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f38,plain,(
% 7.94/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.94/1.49    inference(nnf_transformation,[],[f7])).
% 7.94/1.49  
% 7.94/1.49  fof(f55,plain,(
% 7.94/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.94/1.49    inference(cnf_transformation,[],[f38])).
% 7.94/1.49  
% 7.94/1.49  fof(f54,plain,(
% 7.94/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.94/1.49    inference(cnf_transformation,[],[f38])).
% 7.94/1.49  
% 7.94/1.49  fof(f12,axiom,(
% 7.94/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.94/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f61,plain,(
% 7.94/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.94/1.49    inference(cnf_transformation,[],[f12])).
% 7.94/1.49  
% 7.94/1.49  fof(f2,axiom,(
% 7.94/1.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.94/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f20,plain,(
% 7.94/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.94/1.49    inference(ennf_transformation,[],[f2])).
% 7.94/1.49  
% 7.94/1.49  fof(f21,plain,(
% 7.94/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.94/1.49    inference(flattening,[],[f20])).
% 7.94/1.49  
% 7.94/1.49  fof(f47,plain,(
% 7.94/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.94/1.49    inference(cnf_transformation,[],[f21])).
% 7.94/1.49  
% 7.94/1.49  fof(f75,plain,(
% 7.94/1.49    r1_tarski(sK1,sK2)),
% 7.94/1.49    inference(cnf_transformation,[],[f43])).
% 7.94/1.49  
% 7.94/1.49  fof(f63,plain,(
% 7.94/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.94/1.49    inference(cnf_transformation,[],[f26])).
% 7.94/1.49  
% 7.94/1.49  fof(f11,axiom,(
% 7.94/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.94/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f25,plain,(
% 7.94/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.94/1.49    inference(ennf_transformation,[],[f11])).
% 7.94/1.49  
% 7.94/1.49  fof(f40,plain,(
% 7.94/1.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.94/1.49    inference(nnf_transformation,[],[f25])).
% 7.94/1.49  
% 7.94/1.49  fof(f59,plain,(
% 7.94/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.94/1.49    inference(cnf_transformation,[],[f40])).
% 7.94/1.49  
% 7.94/1.49  fof(f1,axiom,(
% 7.94/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.94/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f34,plain,(
% 7.94/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.94/1.49    inference(nnf_transformation,[],[f1])).
% 7.94/1.49  
% 7.94/1.49  fof(f35,plain,(
% 7.94/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.94/1.49    inference(flattening,[],[f34])).
% 7.94/1.49  
% 7.94/1.49  fof(f46,plain,(
% 7.94/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.94/1.49    inference(cnf_transformation,[],[f35])).
% 7.94/1.49  
% 7.94/1.49  fof(f15,axiom,(
% 7.94/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.94/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f28,plain,(
% 7.94/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.94/1.49    inference(ennf_transformation,[],[f15])).
% 7.94/1.49  
% 7.94/1.49  fof(f29,plain,(
% 7.94/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.94/1.49    inference(flattening,[],[f28])).
% 7.94/1.49  
% 7.94/1.49  fof(f65,plain,(
% 7.94/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.94/1.49    inference(cnf_transformation,[],[f29])).
% 7.94/1.49  
% 7.94/1.49  fof(f77,plain,(
% 7.94/1.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 7.94/1.49    inference(cnf_transformation,[],[f43])).
% 7.94/1.49  
% 7.94/1.49  fof(f72,plain,(
% 7.94/1.49    v1_funct_1(sK3)),
% 7.94/1.49    inference(cnf_transformation,[],[f43])).
% 7.94/1.49  
% 7.94/1.49  fof(f76,plain,(
% 7.94/1.49    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 7.94/1.49    inference(cnf_transformation,[],[f43])).
% 7.94/1.49  
% 7.94/1.49  fof(f45,plain,(
% 7.94/1.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.94/1.49    inference(cnf_transformation,[],[f35])).
% 7.94/1.49  
% 7.94/1.49  fof(f78,plain,(
% 7.94/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.94/1.49    inference(equality_resolution,[],[f45])).
% 7.94/1.49  
% 7.94/1.49  fof(f68,plain,(
% 7.94/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.94/1.49    inference(cnf_transformation,[],[f41])).
% 7.94/1.49  
% 7.94/1.49  fof(f3,axiom,(
% 7.94/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.94/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f48,plain,(
% 7.94/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.94/1.49    inference(cnf_transformation,[],[f3])).
% 7.94/1.49  
% 7.94/1.49  fof(f51,plain,(
% 7.94/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.94/1.49    inference(cnf_transformation,[],[f37])).
% 7.94/1.49  
% 7.94/1.49  fof(f81,plain,(
% 7.94/1.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.94/1.49    inference(equality_resolution,[],[f51])).
% 7.94/1.49  
% 7.94/1.49  fof(f4,axiom,(
% 7.94/1.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 7.94/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f22,plain,(
% 7.94/1.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 7.94/1.49    inference(ennf_transformation,[],[f4])).
% 7.94/1.49  
% 7.94/1.49  fof(f49,plain,(
% 7.94/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 7.94/1.49    inference(cnf_transformation,[],[f22])).
% 7.94/1.49  
% 7.94/1.49  fof(f69,plain,(
% 7.94/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.94/1.49    inference(cnf_transformation,[],[f41])).
% 7.94/1.49  
% 7.94/1.49  fof(f85,plain,(
% 7.94/1.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.94/1.49    inference(equality_resolution,[],[f69])).
% 7.94/1.49  
% 7.94/1.49  fof(f6,axiom,(
% 7.94/1.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.94/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f53,plain,(
% 7.94/1.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.94/1.49    inference(cnf_transformation,[],[f6])).
% 7.94/1.49  
% 7.94/1.49  cnf(c_27,plain,
% 7.94/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.94/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.94/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.94/1.49      | k1_xboole_0 = X2 ),
% 7.94/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_32,negated_conjecture,
% 7.94/1.49      ( v1_funct_2(sK3,sK0,sK1) ),
% 7.94/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_527,plain,
% 7.94/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.94/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.94/1.49      | sK1 != X2
% 7.94/1.49      | sK0 != X1
% 7.94/1.49      | sK3 != X0
% 7.94/1.49      | k1_xboole_0 = X2 ),
% 7.94/1.49      inference(resolution_lifted,[status(thm)],[c_27,c_32]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_528,plain,
% 7.94/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.94/1.49      | k1_relset_1(sK0,sK1,sK3) = sK0
% 7.94/1.49      | k1_xboole_0 = sK1 ),
% 7.94/1.49      inference(unflattening,[status(thm)],[c_527]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_31,negated_conjecture,
% 7.94/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.94/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_530,plain,
% 7.94/1.49      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 7.94/1.49      inference(global_propositional_subsumption,[status(thm)],[c_528,c_31]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1333,plain,
% 7.94/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_20,plain,
% 7.94/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.94/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.94/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1336,plain,
% 7.94/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.94/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2638,plain,
% 7.94/1.49      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_1333,c_1336]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2733,plain,
% 7.94/1.49      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_530,c_2638]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_6,plain,
% 7.94/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.94/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_19,plain,
% 7.94/1.49      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.94/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_14,plain,
% 7.94/1.49      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.94/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_396,plain,
% 7.94/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.94/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 7.94/1.49      | ~ v1_relat_1(X0) ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_19,c_14]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1331,plain,
% 7.94/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.94/1.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.94/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2388,plain,
% 7.94/1.49      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
% 7.94/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_1333,c_1331]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_12,plain,
% 7.94/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.94/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_10,plain,
% 7.94/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.94/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_238,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.94/1.49      inference(prop_impl,[status(thm)],[c_10]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_239,plain,
% 7.94/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.94/1.49      inference(renaming,[status(thm)],[c_238]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_298,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.94/1.49      inference(bin_hyper_res,[status(thm)],[c_12,c_239]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_11,plain,
% 7.94/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.94/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1899,plain,
% 7.94/1.49      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_11,c_31]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2290,plain,
% 7.94/1.49      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_298,c_1899]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_17,plain,
% 7.94/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.94/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2425,plain,
% 7.94/1.49      ( v1_relat_1(sK3) ),
% 7.94/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_2290,c_17]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2426,plain,
% 7.94/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_2425]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2736,plain,
% 7.94/1.49      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
% 7.94/1.49      inference(global_propositional_subsumption,[status(thm)],[c_2388,c_2426]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_3,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.94/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1343,plain,
% 7.94/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.94/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.94/1.49      | r1_tarski(X0,X2) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_3779,plain,
% 7.94/1.49      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 7.94/1.49      | r1_tarski(sK0,X0) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_2736,c_1343]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1339,plain,
% 7.94/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.94/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2514,plain,
% 7.94/1.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.94/1.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.94/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_1339,c_1331]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_6275,plain,
% 7.94/1.49      ( r1_tarski(k1_relat_1(k1_relat_1(sK3)),X0) = iProver_top
% 7.94/1.49      | r1_tarski(sK0,k2_zfmisc_1(X0,X1)) != iProver_top
% 7.94/1.49      | v1_relat_1(k1_relat_1(sK3)) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_3779,c_2514]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_69,plain,
% 7.94/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1332,plain,
% 7.94/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.94/1.49      | v1_relat_1(X1) != iProver_top
% 7.94/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_3470,plain,
% 7.94/1.49      ( v1_relat_1(k1_relat_1(sK3)) = iProver_top
% 7.94/1.49      | v1_relat_1(sK0) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_2736,c_1332]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1586,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 7.94/1.49      | v1_relat_1(X0)
% 7.94/1.49      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_298]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_7730,plain,
% 7.94/1.49      ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
% 7.94/1.49      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 7.94/1.49      | v1_relat_1(sK0) ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_1586]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_7736,plain,
% 7.94/1.49      ( r1_tarski(sK0,k2_zfmisc_1(X0,X1)) != iProver_top
% 7.94/1.49      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
% 7.94/1.49      | v1_relat_1(sK0) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_7730]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_22798,plain,
% 7.94/1.49      ( r1_tarski(sK0,k2_zfmisc_1(X0,X1)) != iProver_top
% 7.94/1.49      | r1_tarski(k1_relat_1(k1_relat_1(sK3)),X0) = iProver_top ),
% 7.94/1.49      inference(global_propositional_subsumption,
% 7.94/1.49                [status(thm)],
% 7.94/1.49                [c_6275,c_69,c_3470,c_7736]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_22799,plain,
% 7.94/1.49      ( r1_tarski(k1_relat_1(k1_relat_1(sK3)),X0) = iProver_top
% 7.94/1.49      | r1_tarski(sK0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.94/1.49      inference(renaming,[status(thm)],[c_22798]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_22808,plain,
% 7.94/1.49      ( r1_tarski(k1_relat_1(k1_relat_1(sK3)),X0) = iProver_top
% 7.94/1.49      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_6,c_22799]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_30,negated_conjecture,
% 7.94/1.49      ( r1_tarski(sK1,sK2) ),
% 7.94/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1334,plain,
% 7.94/1.49      ( r1_tarski(sK1,sK2) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_18,plain,
% 7.94/1.49      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.94/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_16,plain,
% 7.94/1.49      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.94/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_415,plain,
% 7.94/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.94/1.49      | r1_tarski(k2_relat_1(X0),X2)
% 7.94/1.49      | ~ v1_relat_1(X0) ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_18,c_16]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1330,plain,
% 7.94/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.94/1.49      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 7.94/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_415]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1807,plain,
% 7.94/1.49      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
% 7.94/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_1333,c_1330]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_3778,plain,
% 7.94/1.49      ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
% 7.94/1.49      | r1_tarski(sK1,X0) != iProver_top
% 7.94/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_1807,c_1343]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_4902,plain,
% 7.94/1.49      ( r1_tarski(sK1,X0) != iProver_top
% 7.94/1.49      | r1_tarski(k2_relat_1(sK3),X0) = iProver_top ),
% 7.94/1.49      inference(global_propositional_subsumption,[status(thm)],[c_3778,c_2426]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_4903,plain,
% 7.94/1.49      ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
% 7.94/1.49      | r1_tarski(sK1,X0) != iProver_top ),
% 7.94/1.49      inference(renaming,[status(thm)],[c_4902]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_4910,plain,
% 7.94/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.94/1.49      | r1_tarski(k2_relat_1(sK3),X1) = iProver_top
% 7.94/1.49      | r1_tarski(sK1,X0) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_4903,c_1343]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_10717,plain,
% 7.94/1.49      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
% 7.94/1.49      | r1_tarski(sK1,sK1) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_1334,c_4910]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_8310,plain,
% 7.94/1.49      ( r1_tarski(k2_relat_1(sK3),sK1) | ~ v1_relat_1(sK3) ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_415,c_31]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1808,plain,
% 7.94/1.49      ( r1_tarski(k2_relat_1(sK3),sK1) | ~ v1_relat_1(sK3) ),
% 7.94/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_1807]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_8694,plain,
% 7.94/1.49      ( r1_tarski(k2_relat_1(sK3),sK1) ),
% 7.94/1.49      inference(global_propositional_subsumption,
% 7.94/1.49                [status(thm)],
% 7.94/1.49                [c_8310,c_1808,c_2425]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2541,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,sK1) | r1_tarski(X0,sK2) ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_3,c_30]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_8718,plain,
% 7.94/1.49      ( r1_tarski(k2_relat_1(sK3),sK2) ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_8694,c_2541]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_8719,plain,
% 7.94/1.49      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_8718]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_11653,plain,
% 7.94/1.49      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 7.94/1.49      inference(global_propositional_subsumption,
% 7.94/1.49                [status(thm)],
% 7.94/1.49                [c_10717,c_8719]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_11660,plain,
% 7.94/1.49      ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
% 7.94/1.49      | r1_tarski(sK2,X0) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_11653,c_1343]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_0,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.94/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1345,plain,
% 7.94/1.49      ( X0 = X1
% 7.94/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.94/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_12367,plain,
% 7.94/1.49      ( k2_relat_1(sK3) = X0
% 7.94/1.49      | r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
% 7.94/1.49      | r1_tarski(sK2,X0) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_11660,c_1345]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_37,plain,
% 7.94/1.49      ( r1_tarski(sK1,sK2) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1603,plain,
% 7.94/1.49      ( ~ r1_tarski(sK1,sK2) | ~ r1_tarski(sK2,sK1) | sK1 = sK2 ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1604,plain,
% 7.94/1.49      ( sK1 = sK2
% 7.94/1.49      | r1_tarski(sK1,sK2) != iProver_top
% 7.94/1.49      | r1_tarski(sK2,sK1) != iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_1603]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1775,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK2,X0) | r1_tarski(sK2,sK1) ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1776,plain,
% 7.94/1.49      ( r1_tarski(X0,sK1) != iProver_top
% 7.94/1.49      | r1_tarski(sK2,X0) != iProver_top
% 7.94/1.49      | r1_tarski(sK2,sK1) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_1775]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2414,plain,
% 7.94/1.49      ( r1_tarski(k1_relat_1(sK3),sK0) | ~ v1_relat_1(sK3) ),
% 7.94/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_2388]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_21,plain,
% 7.94/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.94/1.49      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.94/1.49      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.94/1.49      | ~ v1_relat_1(X0) ),
% 7.94/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_28,negated_conjecture,
% 7.94/1.49      ( ~ v1_funct_2(sK3,sK0,sK2)
% 7.94/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.94/1.49      | ~ v1_funct_1(sK3) ),
% 7.94/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_33,negated_conjecture,
% 7.94/1.49      ( v1_funct_1(sK3) ),
% 7.94/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_171,plain,
% 7.94/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.94/1.49      | ~ v1_funct_2(sK3,sK0,sK2) ),
% 7.94/1.49      inference(global_propositional_subsumption,[status(thm)],[c_28,c_33]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_172,negated_conjecture,
% 7.94/1.49      ( ~ v1_funct_2(sK3,sK0,sK2)
% 7.94/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 7.94/1.49      inference(renaming,[status(thm)],[c_171]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_538,plain,
% 7.94/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.94/1.49      | sK1 != sK2
% 7.94/1.49      | sK0 != sK0
% 7.94/1.49      | sK3 != sK3 ),
% 7.94/1.49      inference(resolution_lifted,[status(thm)],[c_172,c_32]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_605,plain,
% 7.94/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | sK1 != sK2 ),
% 7.94/1.49      inference(equality_resolution_simp,[status(thm)],[c_538]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_4526,plain,
% 7.94/1.49      ( ~ r1_tarski(k2_relat_1(sK3),sK2)
% 7.94/1.49      | ~ r1_tarski(k1_relat_1(sK3),sK0)
% 7.94/1.49      | ~ v1_relat_1(sK3)
% 7.94/1.49      | sK1 != sK2 ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_21,c_605]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_8716,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,k2_relat_1(sK3)) | r1_tarski(X0,sK1) ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_8694,c_3]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_8717,plain,
% 7.94/1.49      ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
% 7.94/1.49      | r1_tarski(X0,sK1) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_8716]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_14855,plain,
% 7.94/1.49      ( r1_tarski(X0,k2_relat_1(sK3)) != iProver_top
% 7.94/1.49      | r1_tarski(sK2,X0) != iProver_top ),
% 7.94/1.49      inference(global_propositional_subsumption,
% 7.94/1.49                [status(thm)],
% 7.94/1.49                [c_12367,c_37,c_1604,c_1776,c_2414,c_2425,c_4526,c_8717,c_8718]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_23346,plain,
% 7.94/1.49      ( r1_tarski(sK2,k1_relat_1(k1_relat_1(sK3))) != iProver_top
% 7.94/1.49      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_22808,c_14855]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_29,negated_conjecture,
% 7.94/1.49      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 7.94/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1639,plain,
% 7.94/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.94/1.49      | k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_20]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_785,plain,( X0 = X0 ),theory(equality) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1745,plain,
% 7.94/1.49      ( sK0 = sK0 ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_785]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_787,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.94/1.49      theory(equality) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1698,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,X1)
% 7.94/1.49      | r1_tarski(sK0,k1_xboole_0)
% 7.94/1.49      | sK0 != X0
% 7.94/1.49      | k1_xboole_0 != X1 ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_787]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1931,plain,
% 7.94/1.49      ( ~ r1_tarski(sK0,X0)
% 7.94/1.49      | r1_tarski(sK0,k1_xboole_0)
% 7.94/1.49      | sK0 != sK0
% 7.94/1.49      | k1_xboole_0 != X0 ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_1698]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2335,plain,
% 7.94/1.49      ( ~ r1_tarski(sK0,sK0)
% 7.94/1.49      | r1_tarski(sK0,k1_xboole_0)
% 7.94/1.49      | sK0 != sK0
% 7.94/1.49      | k1_xboole_0 != sK0 ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_1931]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2337,plain,
% 7.94/1.49      ( sK0 != sK0
% 7.94/1.49      | k1_xboole_0 != sK0
% 7.94/1.49      | r1_tarski(sK0,sK0) != iProver_top
% 7.94/1.49      | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_2335]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f78]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2336,plain,
% 7.94/1.49      ( r1_tarski(sK0,sK0) ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2339,plain,
% 7.94/1.49      ( r1_tarski(sK0,sK0) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_2336]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_786,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2677,plain,
% 7.94/1.49      ( X0 != X1 | X1 = X0 ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_786,c_785]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_5576,plain,
% 7.94/1.49      ( sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_2677,c_530]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_6114,plain,
% 7.94/1.49      ( X0 != X1
% 7.94/1.49      | X0 = k1_relset_1(sK0,sK1,sK3)
% 7.94/1.49      | k1_relset_1(sK0,sK1,sK3) != X1 ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_786]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_9228,plain,
% 7.94/1.49      ( X0 = k1_relset_1(sK0,sK1,sK3)
% 7.94/1.49      | X0 != k1_relat_1(sK3)
% 7.94/1.49      | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3) ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_6114]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_14613,plain,
% 7.94/1.49      ( k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
% 7.94/1.49      | k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
% 7.94/1.49      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_9228]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_14614,plain,
% 7.94/1.49      ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_785]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_3651,plain,
% 7.94/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.94/1.49      | X3 != k1_relat_1(X0)
% 7.94/1.49      | k1_relset_1(X1,X2,X0) = X3 ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_20,c_786]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_25,plain,
% 7.94/1.49      ( v1_funct_2(X0,X1,X2)
% 7.94/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.94/1.49      | k1_relset_1(X1,X2,X0) != X1
% 7.94/1.49      | k1_xboole_0 = X2 ),
% 7.94/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_514,plain,
% 7.94/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.94/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.94/1.49      | k1_relset_1(X1,X2,X0) != X1
% 7.94/1.49      | sK2 != X2
% 7.94/1.49      | sK0 != X1
% 7.94/1.49      | sK3 != X0
% 7.94/1.49      | k1_xboole_0 = X2 ),
% 7.94/1.49      inference(resolution_lifted,[status(thm)],[c_25,c_172]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_515,plain,
% 7.94/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.94/1.49      | k1_relset_1(sK0,sK2,sK3) != sK0
% 7.94/1.49      | k1_xboole_0 = sK2 ),
% 7.94/1.49      inference(unflattening,[status(thm)],[c_514]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_14508,plain,
% 7.94/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.94/1.49      | sK0 != k1_relat_1(sK3)
% 7.94/1.49      | k1_xboole_0 = sK2 ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_3651,c_515]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1777,plain,
% 7.94/1.49      ( r1_tarski(sK2,sK1)
% 7.94/1.49      | ~ r1_tarski(sK2,k1_xboole_0)
% 7.94/1.49      | ~ r1_tarski(k1_xboole_0,sK1) ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_1775]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2235,plain,
% 7.94/1.49      ( sK2 = sK2 ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_785]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2090,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,X1)
% 7.94/1.49      | r1_tarski(sK2,k1_xboole_0)
% 7.94/1.49      | sK2 != X0
% 7.94/1.49      | k1_xboole_0 != X1 ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_787]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2234,plain,
% 7.94/1.49      ( ~ r1_tarski(sK2,X0)
% 7.94/1.49      | r1_tarski(sK2,k1_xboole_0)
% 7.94/1.49      | sK2 != sK2
% 7.94/1.49      | k1_xboole_0 != X0 ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_2090]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_3445,plain,
% 7.94/1.49      ( ~ r1_tarski(sK2,sK2)
% 7.94/1.49      | r1_tarski(sK2,k1_xboole_0)
% 7.94/1.49      | sK2 != sK2
% 7.94/1.49      | k1_xboole_0 != sK2 ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_2234]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_3446,plain,
% 7.94/1.49      ( r1_tarski(sK2,sK2) ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_4,plain,
% 7.94/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.94/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_7042,plain,
% 7.94/1.49      ( r1_tarski(k1_xboole_0,sK1) ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_14635,plain,
% 7.94/1.49      ( sK0 != k1_relat_1(sK3)
% 7.94/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 7.94/1.49      inference(global_propositional_subsumption,
% 7.94/1.49                [status(thm)],
% 7.94/1.49                [c_14508,c_30,c_1603,c_1777,c_2235,c_2414,c_2425,c_3445,
% 7.94/1.49                 c_3446,c_4526,c_7042,c_8718]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_14636,plain,
% 7.94/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.94/1.49      | sK0 != k1_relat_1(sK3) ),
% 7.94/1.49      inference(renaming,[status(thm)],[c_14635]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_14653,plain,
% 7.94/1.49      ( ~ r1_tarski(k2_relat_1(sK3),sK2)
% 7.94/1.49      | ~ r1_tarski(k1_relat_1(sK3),sK0)
% 7.94/1.49      | ~ v1_relat_1(sK3)
% 7.94/1.49      | sK0 != k1_relat_1(sK3) ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_14636,c_21]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1746,plain,
% 7.94/1.49      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_786]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_3426,plain,
% 7.94/1.49      ( X0 != k1_relset_1(sK0,sK1,sK3)
% 7.94/1.49      | sK0 = X0
% 7.94/1.49      | sK0 != k1_relset_1(sK0,sK1,sK3) ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_1746]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_32838,plain,
% 7.94/1.49      ( k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3)
% 7.94/1.49      | sK0 != k1_relset_1(sK0,sK1,sK3)
% 7.94/1.49      | sK0 = k1_relat_1(sK3) ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_3426]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_33273,plain,
% 7.94/1.49      ( r1_tarski(sK2,k1_relat_1(k1_relat_1(sK3))) != iProver_top ),
% 7.94/1.49      inference(global_propositional_subsumption,
% 7.94/1.49                [status(thm)],
% 7.94/1.49                [c_23346,c_31,c_29,c_1639,c_1745,c_2337,c_2339,c_2414,c_2425,
% 7.94/1.49                 c_5576,c_8718,c_14613,c_14614,c_14653,c_32838]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_33278,plain,
% 7.94/1.49      ( sK1 = k1_xboole_0 | r1_tarski(sK2,k1_relat_1(sK0)) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_2733,c_33273]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1612,plain,
% 7.94/1.49      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_786]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1738,plain,
% 7.94/1.49      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_1612]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1739,plain,
% 7.94/1.49      ( sK1 = sK1 ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_785]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_34245,plain,
% 7.94/1.49      ( sK1 = k1_xboole_0 ),
% 7.94/1.49      inference(global_propositional_subsumption,
% 7.94/1.49                [status(thm)],
% 7.94/1.49                [c_33278,c_31,c_1639,c_1738,c_1739,c_2414,c_2425,c_5576,
% 7.94/1.49                 c_8718,c_14613,c_14614,c_14653,c_32838]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1338,plain,
% 7.94/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.94/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2506,plain,
% 7.94/1.49      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_1333,c_1338]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_34333,plain,
% 7.94/1.49      ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) = iProver_top ),
% 7.94/1.49      inference(demodulation,[status(thm)],[c_34245,c_2506]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_34341,plain,
% 7.94/1.49      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.94/1.49      inference(demodulation,[status(thm)],[c_34245,c_29]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_34342,plain,
% 7.94/1.49      ( sK0 = k1_xboole_0 ),
% 7.94/1.49      inference(equality_resolution_simp,[status(thm)],[c_34341]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_34367,plain,
% 7.94/1.49      ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.94/1.49      inference(light_normalisation,[status(thm)],[c_34333,c_34342]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_7,plain,
% 7.94/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.94/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_34369,plain,
% 7.94/1.49      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 7.94/1.49      inference(demodulation,[status(thm)],[c_34367,c_7]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_5,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 7.94/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1341,plain,
% 7.94/1.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_35292,plain,
% 7.94/1.49      ( sK3 = k1_xboole_0 ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_34369,c_1341]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_24,plain,
% 7.94/1.49      ( v1_funct_2(X0,k1_xboole_0,X1)
% 7.94/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.94/1.49      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 7.94/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_485,plain,
% 7.94/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.94/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.94/1.49      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 7.94/1.49      | sK2 != X1
% 7.94/1.49      | sK0 != k1_xboole_0
% 7.94/1.49      | sK3 != X0 ),
% 7.94/1.49      inference(resolution_lifted,[status(thm)],[c_24,c_172]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_486,plain,
% 7.94/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 7.94/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 7.94/1.49      | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 7.94/1.49      | sK0 != k1_xboole_0 ),
% 7.94/1.49      inference(unflattening,[status(thm)],[c_485]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1327,plain,
% 7.94/1.49      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 7.94/1.49      | sK0 != k1_xboole_0
% 7.94/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 7.94/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1464,plain,
% 7.94/1.49      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 7.94/1.49      | sK0 != k1_xboole_0
% 7.94/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 7.94/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.94/1.49      inference(demodulation,[status(thm)],[c_1327,c_7]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_34716,plain,
% 7.94/1.49      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 7.94/1.49      | k1_xboole_0 != k1_xboole_0
% 7.94/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 7.94/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.94/1.49      inference(demodulation,[status(thm)],[c_34342,c_1464]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_34726,plain,
% 7.94/1.49      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 7.94/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 7.94/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.94/1.49      inference(equality_resolution_simp,[status(thm)],[c_34716]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_34730,plain,
% 7.94/1.49      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 7.94/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.94/1.49      inference(demodulation,[status(thm)],[c_34726,c_7]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1687,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,X1)
% 7.94/1.49      | r1_tarski(sK1,k1_xboole_0)
% 7.94/1.49      | sK1 != X0
% 7.94/1.49      | k1_xboole_0 != X1 ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_787]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1924,plain,
% 7.94/1.49      ( ~ r1_tarski(sK1,X0)
% 7.94/1.49      | r1_tarski(sK1,k1_xboole_0)
% 7.94/1.49      | sK1 != sK1
% 7.94/1.49      | k1_xboole_0 != X0 ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_1687]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2323,plain,
% 7.94/1.49      ( ~ r1_tarski(sK1,sK1)
% 7.94/1.49      | r1_tarski(sK1,k1_xboole_0)
% 7.94/1.49      | sK1 != sK1
% 7.94/1.49      | k1_xboole_0 != sK1 ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_1924]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2325,plain,
% 7.94/1.49      ( sK1 != sK1
% 7.94/1.49      | k1_xboole_0 != sK1
% 7.94/1.49      | r1_tarski(sK1,sK1) != iProver_top
% 7.94/1.49      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_2323]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2324,plain,
% 7.94/1.49      ( r1_tarski(sK1,sK1) ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2327,plain,
% 7.94/1.49      ( r1_tarski(sK1,sK1) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_2324]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1335,plain,
% 7.94/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.94/1.49      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.94/1.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.94/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_4346,plain,
% 7.94/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.94/1.49      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 7.94/1.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.94/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_6,c_1335]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_4633,plain,
% 7.94/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.94/1.49      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 7.94/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_2736,c_4346]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_5015,plain,
% 7.94/1.49      ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 7.94/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.94/1.49      inference(global_propositional_subsumption,[status(thm)],[c_4633,c_2426]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_5016,plain,
% 7.94/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.94/1.49      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 7.94/1.49      inference(renaming,[status(thm)],[c_5015]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_5021,plain,
% 7.94/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.94/1.49      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_4903,c_5016]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_35725,plain,
% 7.94/1.49      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0 ),
% 7.94/1.49      inference(global_propositional_subsumption,
% 7.94/1.49                [status(thm)],
% 7.94/1.49                [c_34730,c_31,c_1639,c_1739,c_2325,c_2327,c_2414,c_2425,
% 7.94/1.49                 c_5021,c_5576,c_8718,c_14613,c_14614,c_14653,c_32838]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_35883,plain,
% 7.94/1.49      ( k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) != k1_xboole_0 ),
% 7.94/1.49      inference(demodulation,[status(thm)],[c_35292,c_35725]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1344,plain,
% 7.94/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2637,plain,
% 7.94/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.94/1.49      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_1339,c_1336]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_9254,plain,
% 7.94/1.49      ( k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_1344,c_2637]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_9310,plain,
% 7.94/1.49      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_7,c_9254]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_9,plain,
% 7.94/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.94/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1340,plain,
% 7.94/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2387,plain,
% 7.94/1.49      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
% 7.94/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_1340,c_1331]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_71,plain,
% 7.94/1.49      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_69]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1587,plain,
% 7.94/1.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.94/1.49      | v1_relat_1(X0) = iProver_top
% 7.94/1.49      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_1586]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1589,plain,
% 7.94/1.49      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 7.94/1.49      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 7.94/1.49      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_1587]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1629,plain,
% 7.94/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1632,plain,
% 7.94/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_1629]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1634,plain,
% 7.94/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_1632]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1953,plain,
% 7.94/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.94/1.49      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1954,plain,
% 7.94/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.94/1.49      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top ),
% 7.94/1.49      inference(predicate_to_equality,[status(thm)],[c_1953]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1956,plain,
% 7.94/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 7.94/1.49      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.94/1.49      inference(instantiation,[status(thm)],[c_1954]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_5127,plain,
% 7.94/1.49      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 7.94/1.49      inference(global_propositional_subsumption,
% 7.94/1.49                [status(thm)],
% 7.94/1.49                [c_2387,c_71,c_1589,c_1634,c_1956]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_5137,plain,
% 7.94/1.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.94/1.49      inference(superposition,[status(thm)],[c_5127,c_1341]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_9312,plain,
% 7.94/1.49      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
% 7.94/1.49      inference(light_normalisation,[status(thm)],[c_9310,c_7,c_5137]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_35947,plain,
% 7.94/1.49      ( k1_xboole_0 != k1_xboole_0 ),
% 7.94/1.49      inference(demodulation,[status(thm)],[c_35883,c_9312]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_35948,plain,
% 7.94/1.49      ( $false ),
% 7.94/1.49      inference(equality_resolution_simp,[status(thm)],[c_35947]) ).
% 7.94/1.49  
% 7.94/1.49  
% 7.94/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.94/1.49  
% 7.94/1.49  ------                               Statistics
% 7.94/1.49  
% 7.94/1.49  ------ Selected
% 7.94/1.49  
% 7.94/1.49  total_time:                             0.851
% 7.94/1.49  
%------------------------------------------------------------------------------
