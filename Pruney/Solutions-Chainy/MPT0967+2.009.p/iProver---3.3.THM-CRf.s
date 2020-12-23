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
% DateTime   : Thu Dec  3 12:00:39 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  156 (6184 expanded)
%              Number of clauses        :  107 (2185 expanded)
%              Number of leaves         :   14 (1146 expanded)
%              Depth                    :   25
%              Number of atoms          :  496 (34668 expanded)
%              Number of equality atoms :  223 (9250 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f50])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f31,plain,
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

fof(f32,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f31])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f47])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_20,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_290,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_291,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),X0)
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_907,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(sK3),X2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != X1
    | sK3 != X0
    | k1_xboole_0 != X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_291])).

cnf(c_908,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_907])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_305,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_306,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_308,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_910,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_908,c_308])).

cnf(c_1741,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK3
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_910])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_31,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_83,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_89,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1922,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_10])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_355,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_351,c_9])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_355])).

cnf(c_1932,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_1933,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1932])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1980,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | r1_tarski(k2_relat_1(sK3),X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2172,plain,
    ( r1_tarski(k2_relat_1(sK3),X0)
    | ~ r1_tarski(k2_relat_1(sK3),sK1)
    | ~ r1_tarski(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_1980])).

cnf(c_2174,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2172])).

cnf(c_2394,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2172])).

cnf(c_2395,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2394])).

cnf(c_1371,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2397,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,X2)
    | X2 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1371])).

cnf(c_2399,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2397])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_995,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_996,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_995])).

cnf(c_998,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_996,c_25])).

cnf(c_1747,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1749,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2287,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1747,c_1749])).

cnf(c_2357,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_998,c_2287])).

cnf(c_1746,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_307,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_1923,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1922])).

cnf(c_2011,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1746,c_30,c_307,c_1923])).

cnf(c_2012,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2011])).

cnf(c_2431,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2357,c_2012])).

cnf(c_22,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_150,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_27])).

cnf(c_151,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(renaming,[status(thm)],[c_150])).

cnf(c_1045,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != sK0
    | sK2 != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_151,c_291])).

cnf(c_1046,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_1045])).

cnf(c_1056,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relat_1(sK3) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1046,c_9,c_356])).

cnf(c_1735,plain,
    ( k1_relat_1(sK3) != sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1056])).

cnf(c_2455,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2357,c_1735])).

cnf(c_2971,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2431,c_2455])).

cnf(c_2994,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1741,c_25,c_30,c_31,c_83,c_89,c_308,c_908,c_1922,c_1932,c_1933,c_2174,c_2395,c_2399,c_2971])).

cnf(c_3001,plain,
    ( sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2994,c_2357])).

cnf(c_1370,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1947,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_2037,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1947])).

cnf(c_1369,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2038,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_891,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_892,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_891])).

cnf(c_1742,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_892])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2209,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_2210,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_2436,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1742,c_23,c_83,c_89,c_2210])).

cnf(c_3195,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3001,c_30,c_31,c_1933,c_2037,c_2038,c_2395,c_2436,c_2971])).

cnf(c_3201,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3195,c_1735])).

cnf(c_3205,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3195,c_2287])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_947,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK1 != X1
    | sK0 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_948,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_947])).

cnf(c_1739,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_948])).

cnf(c_3208,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3195,c_1739])).

cnf(c_3225,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3208])).

cnf(c_3211,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3195,c_1747])).

cnf(c_3228,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3225,c_3211])).

cnf(c_3239,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3205,c_3228])).

cnf(c_3242,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3201,c_3239])).

cnf(c_3243,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3242])).

cnf(c_2969,plain,
    ( k1_relset_1(sK0,X0,sK3) = k1_relat_1(sK3)
    | sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2431,c_1749])).

cnf(c_3429,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2969,c_30,c_31,c_1933,c_2395,c_2971])).

cnf(c_3433,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3429,c_3211])).

cnf(c_1744,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_356])).

cnf(c_3579,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3433,c_1744])).

cnf(c_1751,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1754,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2580,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1751,c_1754])).

cnf(c_3610,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3579,c_2580])).

cnf(c_3524,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3239,c_2012])).

cnf(c_3674,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3610,c_3524])).

cnf(c_82,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3696,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3674,c_82])).

cnf(c_3790,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3243,c_3696])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.11/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.00  
% 2.11/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.11/1.00  
% 2.11/1.00  ------  iProver source info
% 2.11/1.00  
% 2.11/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.11/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.11/1.00  git: non_committed_changes: false
% 2.11/1.00  git: last_make_outside_of_git: false
% 2.11/1.00  
% 2.11/1.00  ------ 
% 2.11/1.00  
% 2.11/1.00  ------ Input Options
% 2.11/1.00  
% 2.11/1.00  --out_options                           all
% 2.11/1.00  --tptp_safe_out                         true
% 2.11/1.00  --problem_path                          ""
% 2.11/1.00  --include_path                          ""
% 2.11/1.00  --clausifier                            res/vclausify_rel
% 2.11/1.00  --clausifier_options                    --mode clausify
% 2.11/1.00  --stdin                                 false
% 2.11/1.00  --stats_out                             all
% 2.11/1.00  
% 2.11/1.00  ------ General Options
% 2.11/1.00  
% 2.11/1.00  --fof                                   false
% 2.11/1.00  --time_out_real                         305.
% 2.11/1.00  --time_out_virtual                      -1.
% 2.11/1.00  --symbol_type_check                     false
% 2.11/1.00  --clausify_out                          false
% 2.11/1.00  --sig_cnt_out                           false
% 2.11/1.00  --trig_cnt_out                          false
% 2.11/1.00  --trig_cnt_out_tolerance                1.
% 2.11/1.00  --trig_cnt_out_sk_spl                   false
% 2.11/1.00  --abstr_cl_out                          false
% 2.11/1.00  
% 2.11/1.00  ------ Global Options
% 2.11/1.00  
% 2.11/1.00  --schedule                              default
% 2.11/1.00  --add_important_lit                     false
% 2.11/1.00  --prop_solver_per_cl                    1000
% 2.11/1.00  --min_unsat_core                        false
% 2.11/1.00  --soft_assumptions                      false
% 2.11/1.00  --soft_lemma_size                       3
% 2.11/1.00  --prop_impl_unit_size                   0
% 2.11/1.00  --prop_impl_unit                        []
% 2.11/1.00  --share_sel_clauses                     true
% 2.11/1.00  --reset_solvers                         false
% 2.11/1.00  --bc_imp_inh                            [conj_cone]
% 2.11/1.00  --conj_cone_tolerance                   3.
% 2.11/1.00  --extra_neg_conj                        none
% 2.11/1.00  --large_theory_mode                     true
% 2.11/1.00  --prolific_symb_bound                   200
% 2.11/1.00  --lt_threshold                          2000
% 2.11/1.00  --clause_weak_htbl                      true
% 2.11/1.00  --gc_record_bc_elim                     false
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing Options
% 2.11/1.00  
% 2.11/1.00  --preprocessing_flag                    true
% 2.11/1.00  --time_out_prep_mult                    0.1
% 2.11/1.00  --splitting_mode                        input
% 2.11/1.00  --splitting_grd                         true
% 2.11/1.00  --splitting_cvd                         false
% 2.11/1.00  --splitting_cvd_svl                     false
% 2.11/1.00  --splitting_nvd                         32
% 2.11/1.00  --sub_typing                            true
% 2.11/1.00  --prep_gs_sim                           true
% 2.11/1.00  --prep_unflatten                        true
% 2.11/1.00  --prep_res_sim                          true
% 2.11/1.00  --prep_upred                            true
% 2.11/1.00  --prep_sem_filter                       exhaustive
% 2.11/1.00  --prep_sem_filter_out                   false
% 2.11/1.00  --pred_elim                             true
% 2.11/1.00  --res_sim_input                         true
% 2.11/1.00  --eq_ax_congr_red                       true
% 2.11/1.00  --pure_diseq_elim                       true
% 2.11/1.00  --brand_transform                       false
% 2.11/1.00  --non_eq_to_eq                          false
% 2.11/1.00  --prep_def_merge                        true
% 2.11/1.00  --prep_def_merge_prop_impl              false
% 2.11/1.00  --prep_def_merge_mbd                    true
% 2.11/1.00  --prep_def_merge_tr_red                 false
% 2.11/1.00  --prep_def_merge_tr_cl                  false
% 2.11/1.00  --smt_preprocessing                     true
% 2.11/1.00  --smt_ac_axioms                         fast
% 2.11/1.00  --preprocessed_out                      false
% 2.11/1.00  --preprocessed_stats                    false
% 2.11/1.00  
% 2.11/1.00  ------ Abstraction refinement Options
% 2.11/1.00  
% 2.11/1.00  --abstr_ref                             []
% 2.11/1.00  --abstr_ref_prep                        false
% 2.11/1.00  --abstr_ref_until_sat                   false
% 2.11/1.00  --abstr_ref_sig_restrict                funpre
% 2.11/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.11/1.00  --abstr_ref_under                       []
% 2.11/1.00  
% 2.11/1.00  ------ SAT Options
% 2.11/1.00  
% 2.11/1.00  --sat_mode                              false
% 2.11/1.00  --sat_fm_restart_options                ""
% 2.11/1.00  --sat_gr_def                            false
% 2.11/1.00  --sat_epr_types                         true
% 2.11/1.00  --sat_non_cyclic_types                  false
% 2.11/1.00  --sat_finite_models                     false
% 2.11/1.00  --sat_fm_lemmas                         false
% 2.11/1.00  --sat_fm_prep                           false
% 2.11/1.00  --sat_fm_uc_incr                        true
% 2.11/1.00  --sat_out_model                         small
% 2.11/1.00  --sat_out_clauses                       false
% 2.11/1.00  
% 2.11/1.00  ------ QBF Options
% 2.11/1.00  
% 2.11/1.00  --qbf_mode                              false
% 2.11/1.00  --qbf_elim_univ                         false
% 2.11/1.00  --qbf_dom_inst                          none
% 2.11/1.00  --qbf_dom_pre_inst                      false
% 2.11/1.00  --qbf_sk_in                             false
% 2.11/1.00  --qbf_pred_elim                         true
% 2.11/1.00  --qbf_split                             512
% 2.11/1.00  
% 2.11/1.00  ------ BMC1 Options
% 2.11/1.00  
% 2.11/1.00  --bmc1_incremental                      false
% 2.11/1.00  --bmc1_axioms                           reachable_all
% 2.11/1.00  --bmc1_min_bound                        0
% 2.11/1.00  --bmc1_max_bound                        -1
% 2.11/1.00  --bmc1_max_bound_default                -1
% 2.11/1.00  --bmc1_symbol_reachability              true
% 2.11/1.00  --bmc1_property_lemmas                  false
% 2.11/1.00  --bmc1_k_induction                      false
% 2.11/1.00  --bmc1_non_equiv_states                 false
% 2.11/1.00  --bmc1_deadlock                         false
% 2.11/1.00  --bmc1_ucm                              false
% 2.11/1.00  --bmc1_add_unsat_core                   none
% 2.11/1.00  --bmc1_unsat_core_children              false
% 2.11/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.11/1.00  --bmc1_out_stat                         full
% 2.11/1.00  --bmc1_ground_init                      false
% 2.11/1.00  --bmc1_pre_inst_next_state              false
% 2.11/1.00  --bmc1_pre_inst_state                   false
% 2.11/1.00  --bmc1_pre_inst_reach_state             false
% 2.11/1.00  --bmc1_out_unsat_core                   false
% 2.11/1.00  --bmc1_aig_witness_out                  false
% 2.11/1.00  --bmc1_verbose                          false
% 2.11/1.00  --bmc1_dump_clauses_tptp                false
% 2.11/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.11/1.00  --bmc1_dump_file                        -
% 2.11/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.11/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.11/1.00  --bmc1_ucm_extend_mode                  1
% 2.11/1.00  --bmc1_ucm_init_mode                    2
% 2.11/1.00  --bmc1_ucm_cone_mode                    none
% 2.11/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.11/1.00  --bmc1_ucm_relax_model                  4
% 2.11/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.11/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.11/1.00  --bmc1_ucm_layered_model                none
% 2.11/1.00  --bmc1_ucm_max_lemma_size               10
% 2.11/1.00  
% 2.11/1.00  ------ AIG Options
% 2.11/1.00  
% 2.11/1.00  --aig_mode                              false
% 2.11/1.00  
% 2.11/1.00  ------ Instantiation Options
% 2.11/1.00  
% 2.11/1.00  --instantiation_flag                    true
% 2.11/1.00  --inst_sos_flag                         false
% 2.11/1.00  --inst_sos_phase                        true
% 2.11/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.11/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.11/1.00  --inst_lit_sel_side                     num_symb
% 2.11/1.00  --inst_solver_per_active                1400
% 2.11/1.00  --inst_solver_calls_frac                1.
% 2.11/1.00  --inst_passive_queue_type               priority_queues
% 2.11/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.11/1.00  --inst_passive_queues_freq              [25;2]
% 2.11/1.00  --inst_dismatching                      true
% 2.11/1.00  --inst_eager_unprocessed_to_passive     true
% 2.11/1.00  --inst_prop_sim_given                   true
% 2.11/1.00  --inst_prop_sim_new                     false
% 2.11/1.00  --inst_subs_new                         false
% 2.11/1.00  --inst_eq_res_simp                      false
% 2.11/1.00  --inst_subs_given                       false
% 2.11/1.00  --inst_orphan_elimination               true
% 2.11/1.00  --inst_learning_loop_flag               true
% 2.11/1.00  --inst_learning_start                   3000
% 2.11/1.00  --inst_learning_factor                  2
% 2.11/1.00  --inst_start_prop_sim_after_learn       3
% 2.11/1.00  --inst_sel_renew                        solver
% 2.11/1.00  --inst_lit_activity_flag                true
% 2.11/1.00  --inst_restr_to_given                   false
% 2.11/1.00  --inst_activity_threshold               500
% 2.11/1.00  --inst_out_proof                        true
% 2.11/1.00  
% 2.11/1.00  ------ Resolution Options
% 2.11/1.00  
% 2.11/1.00  --resolution_flag                       true
% 2.11/1.00  --res_lit_sel                           adaptive
% 2.11/1.00  --res_lit_sel_side                      none
% 2.11/1.00  --res_ordering                          kbo
% 2.11/1.00  --res_to_prop_solver                    active
% 2.11/1.00  --res_prop_simpl_new                    false
% 2.11/1.00  --res_prop_simpl_given                  true
% 2.11/1.00  --res_passive_queue_type                priority_queues
% 2.11/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.11/1.00  --res_passive_queues_freq               [15;5]
% 2.11/1.00  --res_forward_subs                      full
% 2.11/1.00  --res_backward_subs                     full
% 2.11/1.00  --res_forward_subs_resolution           true
% 2.11/1.00  --res_backward_subs_resolution          true
% 2.11/1.00  --res_orphan_elimination                true
% 2.11/1.00  --res_time_limit                        2.
% 2.11/1.00  --res_out_proof                         true
% 2.11/1.00  
% 2.11/1.00  ------ Superposition Options
% 2.11/1.00  
% 2.11/1.00  --superposition_flag                    true
% 2.11/1.00  --sup_passive_queue_type                priority_queues
% 2.11/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.11/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.11/1.00  --demod_completeness_check              fast
% 2.11/1.00  --demod_use_ground                      true
% 2.11/1.00  --sup_to_prop_solver                    passive
% 2.11/1.00  --sup_prop_simpl_new                    true
% 2.11/1.00  --sup_prop_simpl_given                  true
% 2.11/1.00  --sup_fun_splitting                     false
% 2.11/1.00  --sup_smt_interval                      50000
% 2.11/1.00  
% 2.11/1.00  ------ Superposition Simplification Setup
% 2.11/1.00  
% 2.11/1.00  --sup_indices_passive                   []
% 2.11/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.11/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.00  --sup_full_bw                           [BwDemod]
% 2.11/1.00  --sup_immed_triv                        [TrivRules]
% 2.11/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.11/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.00  --sup_immed_bw_main                     []
% 2.11/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.11/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.00  
% 2.11/1.00  ------ Combination Options
% 2.11/1.00  
% 2.11/1.00  --comb_res_mult                         3
% 2.11/1.00  --comb_sup_mult                         2
% 2.11/1.00  --comb_inst_mult                        10
% 2.11/1.00  
% 2.11/1.00  ------ Debug Options
% 2.11/1.00  
% 2.11/1.00  --dbg_backtrace                         false
% 2.11/1.00  --dbg_dump_prop_clauses                 false
% 2.11/1.00  --dbg_dump_prop_clauses_file            -
% 2.11/1.00  --dbg_out_stat                          false
% 2.11/1.00  ------ Parsing...
% 2.11/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.11/1.00  ------ Proving...
% 2.11/1.00  ------ Problem Properties 
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  clauses                                 23
% 2.11/1.00  conjectures                             3
% 2.11/1.00  EPR                                     6
% 2.11/1.00  Horn                                    19
% 2.11/1.00  unary                                   4
% 2.11/1.00  binary                                  8
% 2.11/1.00  lits                                    59
% 2.11/1.00  lits eq                                 26
% 2.11/1.00  fd_pure                                 0
% 2.11/1.00  fd_pseudo                               0
% 2.11/1.00  fd_cond                                 1
% 2.11/1.00  fd_pseudo_cond                          1
% 2.11/1.00  AC symbols                              0
% 2.11/1.00  
% 2.11/1.00  ------ Schedule dynamic 5 is on 
% 2.11/1.00  
% 2.11/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  ------ 
% 2.11/1.00  Current options:
% 2.11/1.00  ------ 
% 2.11/1.00  
% 2.11/1.00  ------ Input Options
% 2.11/1.00  
% 2.11/1.00  --out_options                           all
% 2.11/1.00  --tptp_safe_out                         true
% 2.11/1.00  --problem_path                          ""
% 2.11/1.00  --include_path                          ""
% 2.11/1.00  --clausifier                            res/vclausify_rel
% 2.11/1.00  --clausifier_options                    --mode clausify
% 2.11/1.00  --stdin                                 false
% 2.11/1.00  --stats_out                             all
% 2.11/1.00  
% 2.11/1.00  ------ General Options
% 2.11/1.00  
% 2.11/1.00  --fof                                   false
% 2.11/1.00  --time_out_real                         305.
% 2.11/1.00  --time_out_virtual                      -1.
% 2.11/1.00  --symbol_type_check                     false
% 2.11/1.00  --clausify_out                          false
% 2.11/1.00  --sig_cnt_out                           false
% 2.11/1.00  --trig_cnt_out                          false
% 2.11/1.00  --trig_cnt_out_tolerance                1.
% 2.11/1.00  --trig_cnt_out_sk_spl                   false
% 2.11/1.00  --abstr_cl_out                          false
% 2.11/1.00  
% 2.11/1.00  ------ Global Options
% 2.11/1.00  
% 2.11/1.00  --schedule                              default
% 2.11/1.00  --add_important_lit                     false
% 2.11/1.00  --prop_solver_per_cl                    1000
% 2.11/1.00  --min_unsat_core                        false
% 2.11/1.00  --soft_assumptions                      false
% 2.11/1.00  --soft_lemma_size                       3
% 2.11/1.00  --prop_impl_unit_size                   0
% 2.11/1.00  --prop_impl_unit                        []
% 2.11/1.00  --share_sel_clauses                     true
% 2.11/1.00  --reset_solvers                         false
% 2.11/1.00  --bc_imp_inh                            [conj_cone]
% 2.11/1.00  --conj_cone_tolerance                   3.
% 2.11/1.00  --extra_neg_conj                        none
% 2.11/1.00  --large_theory_mode                     true
% 2.11/1.00  --prolific_symb_bound                   200
% 2.11/1.00  --lt_threshold                          2000
% 2.11/1.00  --clause_weak_htbl                      true
% 2.11/1.00  --gc_record_bc_elim                     false
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing Options
% 2.11/1.00  
% 2.11/1.00  --preprocessing_flag                    true
% 2.11/1.00  --time_out_prep_mult                    0.1
% 2.11/1.00  --splitting_mode                        input
% 2.11/1.00  --splitting_grd                         true
% 2.11/1.00  --splitting_cvd                         false
% 2.11/1.00  --splitting_cvd_svl                     false
% 2.11/1.00  --splitting_nvd                         32
% 2.11/1.00  --sub_typing                            true
% 2.11/1.00  --prep_gs_sim                           true
% 2.11/1.00  --prep_unflatten                        true
% 2.11/1.00  --prep_res_sim                          true
% 2.11/1.00  --prep_upred                            true
% 2.11/1.00  --prep_sem_filter                       exhaustive
% 2.11/1.00  --prep_sem_filter_out                   false
% 2.11/1.00  --pred_elim                             true
% 2.11/1.00  --res_sim_input                         true
% 2.11/1.00  --eq_ax_congr_red                       true
% 2.11/1.00  --pure_diseq_elim                       true
% 2.11/1.00  --brand_transform                       false
% 2.11/1.00  --non_eq_to_eq                          false
% 2.11/1.00  --prep_def_merge                        true
% 2.11/1.00  --prep_def_merge_prop_impl              false
% 2.11/1.00  --prep_def_merge_mbd                    true
% 2.11/1.00  --prep_def_merge_tr_red                 false
% 2.11/1.00  --prep_def_merge_tr_cl                  false
% 2.11/1.00  --smt_preprocessing                     true
% 2.11/1.00  --smt_ac_axioms                         fast
% 2.11/1.00  --preprocessed_out                      false
% 2.11/1.00  --preprocessed_stats                    false
% 2.11/1.00  
% 2.11/1.00  ------ Abstraction refinement Options
% 2.11/1.00  
% 2.11/1.00  --abstr_ref                             []
% 2.11/1.00  --abstr_ref_prep                        false
% 2.11/1.00  --abstr_ref_until_sat                   false
% 2.11/1.00  --abstr_ref_sig_restrict                funpre
% 2.11/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.11/1.00  --abstr_ref_under                       []
% 2.11/1.00  
% 2.11/1.00  ------ SAT Options
% 2.11/1.00  
% 2.11/1.00  --sat_mode                              false
% 2.11/1.00  --sat_fm_restart_options                ""
% 2.11/1.00  --sat_gr_def                            false
% 2.11/1.00  --sat_epr_types                         true
% 2.11/1.00  --sat_non_cyclic_types                  false
% 2.11/1.00  --sat_finite_models                     false
% 2.11/1.00  --sat_fm_lemmas                         false
% 2.11/1.00  --sat_fm_prep                           false
% 2.11/1.00  --sat_fm_uc_incr                        true
% 2.11/1.00  --sat_out_model                         small
% 2.11/1.00  --sat_out_clauses                       false
% 2.11/1.00  
% 2.11/1.00  ------ QBF Options
% 2.11/1.00  
% 2.11/1.00  --qbf_mode                              false
% 2.11/1.00  --qbf_elim_univ                         false
% 2.11/1.00  --qbf_dom_inst                          none
% 2.11/1.00  --qbf_dom_pre_inst                      false
% 2.11/1.00  --qbf_sk_in                             false
% 2.11/1.00  --qbf_pred_elim                         true
% 2.11/1.00  --qbf_split                             512
% 2.11/1.00  
% 2.11/1.00  ------ BMC1 Options
% 2.11/1.00  
% 2.11/1.00  --bmc1_incremental                      false
% 2.11/1.00  --bmc1_axioms                           reachable_all
% 2.11/1.00  --bmc1_min_bound                        0
% 2.11/1.00  --bmc1_max_bound                        -1
% 2.11/1.00  --bmc1_max_bound_default                -1
% 2.11/1.00  --bmc1_symbol_reachability              true
% 2.11/1.00  --bmc1_property_lemmas                  false
% 2.11/1.00  --bmc1_k_induction                      false
% 2.11/1.00  --bmc1_non_equiv_states                 false
% 2.11/1.00  --bmc1_deadlock                         false
% 2.11/1.00  --bmc1_ucm                              false
% 2.11/1.00  --bmc1_add_unsat_core                   none
% 2.11/1.00  --bmc1_unsat_core_children              false
% 2.11/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.11/1.00  --bmc1_out_stat                         full
% 2.11/1.00  --bmc1_ground_init                      false
% 2.11/1.00  --bmc1_pre_inst_next_state              false
% 2.11/1.00  --bmc1_pre_inst_state                   false
% 2.11/1.00  --bmc1_pre_inst_reach_state             false
% 2.11/1.00  --bmc1_out_unsat_core                   false
% 2.11/1.00  --bmc1_aig_witness_out                  false
% 2.11/1.00  --bmc1_verbose                          false
% 2.11/1.00  --bmc1_dump_clauses_tptp                false
% 2.11/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.11/1.00  --bmc1_dump_file                        -
% 2.11/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.11/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.11/1.00  --bmc1_ucm_extend_mode                  1
% 2.11/1.00  --bmc1_ucm_init_mode                    2
% 2.11/1.00  --bmc1_ucm_cone_mode                    none
% 2.11/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.11/1.00  --bmc1_ucm_relax_model                  4
% 2.11/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.11/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.11/1.00  --bmc1_ucm_layered_model                none
% 2.11/1.00  --bmc1_ucm_max_lemma_size               10
% 2.11/1.00  
% 2.11/1.00  ------ AIG Options
% 2.11/1.00  
% 2.11/1.00  --aig_mode                              false
% 2.11/1.00  
% 2.11/1.00  ------ Instantiation Options
% 2.11/1.00  
% 2.11/1.00  --instantiation_flag                    true
% 2.11/1.00  --inst_sos_flag                         false
% 2.11/1.00  --inst_sos_phase                        true
% 2.11/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.11/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.11/1.00  --inst_lit_sel_side                     none
% 2.11/1.00  --inst_solver_per_active                1400
% 2.11/1.00  --inst_solver_calls_frac                1.
% 2.11/1.00  --inst_passive_queue_type               priority_queues
% 2.11/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.11/1.00  --inst_passive_queues_freq              [25;2]
% 2.11/1.00  --inst_dismatching                      true
% 2.11/1.00  --inst_eager_unprocessed_to_passive     true
% 2.11/1.00  --inst_prop_sim_given                   true
% 2.11/1.00  --inst_prop_sim_new                     false
% 2.11/1.00  --inst_subs_new                         false
% 2.11/1.00  --inst_eq_res_simp                      false
% 2.11/1.00  --inst_subs_given                       false
% 2.11/1.00  --inst_orphan_elimination               true
% 2.11/1.00  --inst_learning_loop_flag               true
% 2.11/1.00  --inst_learning_start                   3000
% 2.11/1.00  --inst_learning_factor                  2
% 2.11/1.00  --inst_start_prop_sim_after_learn       3
% 2.11/1.00  --inst_sel_renew                        solver
% 2.11/1.00  --inst_lit_activity_flag                true
% 2.11/1.00  --inst_restr_to_given                   false
% 2.11/1.00  --inst_activity_threshold               500
% 2.11/1.00  --inst_out_proof                        true
% 2.11/1.00  
% 2.11/1.00  ------ Resolution Options
% 2.11/1.00  
% 2.11/1.00  --resolution_flag                       false
% 2.11/1.00  --res_lit_sel                           adaptive
% 2.11/1.00  --res_lit_sel_side                      none
% 2.11/1.00  --res_ordering                          kbo
% 2.11/1.00  --res_to_prop_solver                    active
% 2.11/1.00  --res_prop_simpl_new                    false
% 2.11/1.00  --res_prop_simpl_given                  true
% 2.11/1.00  --res_passive_queue_type                priority_queues
% 2.11/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.11/1.00  --res_passive_queues_freq               [15;5]
% 2.11/1.00  --res_forward_subs                      full
% 2.11/1.00  --res_backward_subs                     full
% 2.11/1.00  --res_forward_subs_resolution           true
% 2.11/1.00  --res_backward_subs_resolution          true
% 2.11/1.00  --res_orphan_elimination                true
% 2.11/1.00  --res_time_limit                        2.
% 2.11/1.00  --res_out_proof                         true
% 2.11/1.00  
% 2.11/1.00  ------ Superposition Options
% 2.11/1.00  
% 2.11/1.00  --superposition_flag                    true
% 2.11/1.00  --sup_passive_queue_type                priority_queues
% 2.11/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.11/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.11/1.00  --demod_completeness_check              fast
% 2.11/1.00  --demod_use_ground                      true
% 2.11/1.00  --sup_to_prop_solver                    passive
% 2.11/1.00  --sup_prop_simpl_new                    true
% 2.11/1.00  --sup_prop_simpl_given                  true
% 2.11/1.00  --sup_fun_splitting                     false
% 2.11/1.00  --sup_smt_interval                      50000
% 2.11/1.00  
% 2.11/1.00  ------ Superposition Simplification Setup
% 2.11/1.00  
% 2.11/1.00  --sup_indices_passive                   []
% 2.11/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.11/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.00  --sup_full_bw                           [BwDemod]
% 2.11/1.00  --sup_immed_triv                        [TrivRules]
% 2.11/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.11/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.00  --sup_immed_bw_main                     []
% 2.11/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.11/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.00  
% 2.11/1.00  ------ Combination Options
% 2.11/1.00  
% 2.11/1.00  --comb_res_mult                         3
% 2.11/1.00  --comb_sup_mult                         2
% 2.11/1.00  --comb_inst_mult                        10
% 2.11/1.00  
% 2.11/1.00  ------ Debug Options
% 2.11/1.00  
% 2.11/1.00  --dbg_backtrace                         false
% 2.11/1.00  --dbg_dump_prop_clauses                 false
% 2.11/1.00  --dbg_dump_prop_clauses_file            -
% 2.11/1.00  --dbg_out_stat                          false
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  ------ Proving...
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  % SZS status Theorem for theBenchmark.p
% 2.11/1.00  
% 2.11/1.00   Resolution empty clause
% 2.11/1.00  
% 2.11/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.11/1.00  
% 2.11/1.00  fof(f9,axiom,(
% 2.11/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f20,plain,(
% 2.11/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.11/1.00    inference(ennf_transformation,[],[f9])).
% 2.11/1.00  
% 2.11/1.00  fof(f21,plain,(
% 2.11/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.11/1.00    inference(flattening,[],[f20])).
% 2.11/1.00  
% 2.11/1.00  fof(f30,plain,(
% 2.11/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.11/1.00    inference(nnf_transformation,[],[f21])).
% 2.11/1.00  
% 2.11/1.00  fof(f50,plain,(
% 2.11/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.11/1.00    inference(cnf_transformation,[],[f30])).
% 2.11/1.00  
% 2.11/1.00  fof(f65,plain,(
% 2.11/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.11/1.00    inference(equality_resolution,[],[f50])).
% 2.11/1.00  
% 2.11/1.00  fof(f10,axiom,(
% 2.11/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f22,plain,(
% 2.11/1.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.11/1.00    inference(ennf_transformation,[],[f10])).
% 2.11/1.00  
% 2.11/1.00  fof(f23,plain,(
% 2.11/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.11/1.00    inference(flattening,[],[f22])).
% 2.11/1.00  
% 2.11/1.00  fof(f53,plain,(
% 2.11/1.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.11/1.00    inference(cnf_transformation,[],[f23])).
% 2.11/1.00  
% 2.11/1.00  fof(f11,conjecture,(
% 2.11/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f12,negated_conjecture,(
% 2.11/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.11/1.00    inference(negated_conjecture,[],[f11])).
% 2.11/1.00  
% 2.11/1.00  fof(f24,plain,(
% 2.11/1.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.11/1.00    inference(ennf_transformation,[],[f12])).
% 2.11/1.00  
% 2.11/1.00  fof(f25,plain,(
% 2.11/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.11/1.00    inference(flattening,[],[f24])).
% 2.11/1.00  
% 2.11/1.00  fof(f31,plain,(
% 2.11/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.11/1.00    introduced(choice_axiom,[])).
% 2.11/1.00  
% 2.11/1.00  fof(f32,plain,(
% 2.11/1.00    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.11/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f31])).
% 2.11/1.00  
% 2.11/1.00  fof(f55,plain,(
% 2.11/1.00    v1_funct_1(sK3)),
% 2.11/1.00    inference(cnf_transformation,[],[f32])).
% 2.11/1.00  
% 2.11/1.00  fof(f54,plain,(
% 2.11/1.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.11/1.00    inference(cnf_transformation,[],[f23])).
% 2.11/1.00  
% 2.11/1.00  fof(f57,plain,(
% 2.11/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.11/1.00    inference(cnf_transformation,[],[f32])).
% 2.11/1.00  
% 2.11/1.00  fof(f58,plain,(
% 2.11/1.00    r1_tarski(sK1,sK2)),
% 2.11/1.00    inference(cnf_transformation,[],[f32])).
% 2.11/1.00  
% 2.11/1.00  fof(f3,axiom,(
% 2.11/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f37,plain,(
% 2.11/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.11/1.00    inference(cnf_transformation,[],[f3])).
% 2.11/1.00  
% 2.11/1.00  fof(f1,axiom,(
% 2.11/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f26,plain,(
% 2.11/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/1.00    inference(nnf_transformation,[],[f1])).
% 2.11/1.00  
% 2.11/1.00  fof(f27,plain,(
% 2.11/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/1.00    inference(flattening,[],[f26])).
% 2.11/1.00  
% 2.11/1.00  fof(f35,plain,(
% 2.11/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.11/1.00    inference(cnf_transformation,[],[f27])).
% 2.11/1.00  
% 2.11/1.00  fof(f6,axiom,(
% 2.11/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f17,plain,(
% 2.11/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.11/1.00    inference(ennf_transformation,[],[f6])).
% 2.11/1.00  
% 2.11/1.00  fof(f42,plain,(
% 2.11/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.11/1.00    inference(cnf_transformation,[],[f17])).
% 2.11/1.00  
% 2.11/1.00  fof(f5,axiom,(
% 2.11/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f16,plain,(
% 2.11/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.11/1.00    inference(ennf_transformation,[],[f5])).
% 2.11/1.00  
% 2.11/1.00  fof(f29,plain,(
% 2.11/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.11/1.00    inference(nnf_transformation,[],[f16])).
% 2.11/1.00  
% 2.11/1.00  fof(f40,plain,(
% 2.11/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.11/1.00    inference(cnf_transformation,[],[f29])).
% 2.11/1.00  
% 2.11/1.00  fof(f7,axiom,(
% 2.11/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f18,plain,(
% 2.11/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.11/1.00    inference(ennf_transformation,[],[f7])).
% 2.11/1.00  
% 2.11/1.00  fof(f44,plain,(
% 2.11/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.11/1.00    inference(cnf_transformation,[],[f18])).
% 2.11/1.00  
% 2.11/1.00  fof(f2,axiom,(
% 2.11/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f13,plain,(
% 2.11/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.11/1.00    inference(ennf_transformation,[],[f2])).
% 2.11/1.00  
% 2.11/1.00  fof(f14,plain,(
% 2.11/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.11/1.00    inference(flattening,[],[f13])).
% 2.11/1.00  
% 2.11/1.00  fof(f36,plain,(
% 2.11/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.11/1.00    inference(cnf_transformation,[],[f14])).
% 2.11/1.00  
% 2.11/1.00  fof(f46,plain,(
% 2.11/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.11/1.00    inference(cnf_transformation,[],[f30])).
% 2.11/1.00  
% 2.11/1.00  fof(f56,plain,(
% 2.11/1.00    v1_funct_2(sK3,sK0,sK1)),
% 2.11/1.00    inference(cnf_transformation,[],[f32])).
% 2.11/1.00  
% 2.11/1.00  fof(f8,axiom,(
% 2.11/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f19,plain,(
% 2.11/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.11/1.00    inference(ennf_transformation,[],[f8])).
% 2.11/1.00  
% 2.11/1.00  fof(f45,plain,(
% 2.11/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.11/1.00    inference(cnf_transformation,[],[f19])).
% 2.11/1.00  
% 2.11/1.00  fof(f60,plain,(
% 2.11/1.00    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 2.11/1.00    inference(cnf_transformation,[],[f32])).
% 2.11/1.00  
% 2.11/1.00  fof(f59,plain,(
% 2.11/1.00    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 2.11/1.00    inference(cnf_transformation,[],[f32])).
% 2.11/1.00  
% 2.11/1.00  fof(f47,plain,(
% 2.11/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.11/1.00    inference(cnf_transformation,[],[f30])).
% 2.11/1.00  
% 2.11/1.00  fof(f67,plain,(
% 2.11/1.00    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.11/1.00    inference(equality_resolution,[],[f47])).
% 2.11/1.00  
% 2.11/1.00  cnf(c_14,plain,
% 2.11/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.11/1.00      | k1_xboole_0 = X1
% 2.11/1.00      | k1_xboole_0 = X0 ),
% 2.11/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_20,plain,
% 2.11/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.11/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.11/1.00      | ~ v1_funct_1(X0)
% 2.11/1.00      | ~ v1_relat_1(X0) ),
% 2.11/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_27,negated_conjecture,
% 2.11/1.00      ( v1_funct_1(sK3) ),
% 2.11/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_290,plain,
% 2.11/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.11/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.11/1.00      | ~ v1_relat_1(X0)
% 2.11/1.00      | sK3 != X0 ),
% 2.11/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_291,plain,
% 2.11/1.00      ( v1_funct_2(sK3,k1_relat_1(sK3),X0)
% 2.11/1.00      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 2.11/1.00      | ~ v1_relat_1(sK3) ),
% 2.11/1.00      inference(unflattening,[status(thm)],[c_290]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_907,plain,
% 2.11/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.11/1.00      | ~ r1_tarski(k2_relat_1(sK3),X2)
% 2.11/1.00      | ~ v1_relat_1(sK3)
% 2.11/1.00      | k1_relat_1(sK3) != X1
% 2.11/1.00      | sK3 != X0
% 2.11/1.00      | k1_xboole_0 != X2
% 2.11/1.00      | k1_xboole_0 = X0
% 2.11/1.00      | k1_xboole_0 = X1 ),
% 2.11/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_291]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_908,plain,
% 2.11/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
% 2.11/1.00      | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
% 2.11/1.00      | ~ v1_relat_1(sK3)
% 2.11/1.00      | k1_xboole_0 = k1_relat_1(sK3)
% 2.11/1.00      | k1_xboole_0 = sK3 ),
% 2.11/1.00      inference(unflattening,[status(thm)],[c_907]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_19,plain,
% 2.11/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.11/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.11/1.00      | ~ v1_funct_1(X0)
% 2.11/1.00      | ~ v1_relat_1(X0) ),
% 2.11/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_305,plain,
% 2.11/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.11/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.11/1.00      | ~ v1_relat_1(X0)
% 2.11/1.00      | sK3 != X0 ),
% 2.11/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_306,plain,
% 2.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
% 2.11/1.00      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 2.11/1.00      | ~ v1_relat_1(sK3) ),
% 2.11/1.00      inference(unflattening,[status(thm)],[c_305]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_308,plain,
% 2.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
% 2.11/1.00      | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
% 2.11/1.00      | ~ v1_relat_1(sK3) ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_306]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_910,plain,
% 2.11/1.00      ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
% 2.11/1.00      | ~ v1_relat_1(sK3)
% 2.11/1.00      | k1_xboole_0 = k1_relat_1(sK3)
% 2.11/1.00      | k1_xboole_0 = sK3 ),
% 2.11/1.00      inference(global_propositional_subsumption,[status(thm)],[c_908,c_308]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1741,plain,
% 2.11/1.00      ( k1_xboole_0 = k1_relat_1(sK3)
% 2.11/1.00      | k1_xboole_0 = sK3
% 2.11/1.00      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 2.11/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_910]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_25,negated_conjecture,
% 2.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.11/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_30,plain,
% 2.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_24,negated_conjecture,
% 2.11/1.00      ( r1_tarski(sK1,sK2) ),
% 2.11/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_31,plain,
% 2.11/1.00      ( r1_tarski(sK1,sK2) = iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_4,plain,
% 2.11/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.11/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_83,plain,
% 2.11/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_0,plain,
% 2.11/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.11/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_89,plain,
% 2.11/1.00      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_9,plain,
% 2.11/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.11/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1922,plain,
% 2.11/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.11/1.00      | v1_relat_1(sK3) ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_8,plain,
% 2.11/1.00      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.11/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_10,plain,
% 2.11/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v5_relat_1(X0,X2) ),
% 2.11/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_350,plain,
% 2.11/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.11/1.00      | r1_tarski(k2_relat_1(X3),X4)
% 2.11/1.00      | ~ v1_relat_1(X3)
% 2.11/1.00      | X0 != X3
% 2.11/1.00      | X2 != X4 ),
% 2.11/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_10]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_351,plain,
% 2.11/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.11/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 2.11/1.00      | ~ v1_relat_1(X0) ),
% 2.11/1.00      inference(unflattening,[status(thm)],[c_350]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_355,plain,
% 2.11/1.00      ( r1_tarski(k2_relat_1(X0),X2)
% 2.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.11/1.00      inference(global_propositional_subsumption,[status(thm)],[c_351,c_9]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_356,plain,
% 2.11/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.11/1.00      | r1_tarski(k2_relat_1(X0),X2) ),
% 2.11/1.00      inference(renaming,[status(thm)],[c_355]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1932,plain,
% 2.11/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.11/1.00      | r1_tarski(k2_relat_1(sK3),sK1) ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_356]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1933,plain,
% 2.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.11/1.00      | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1932]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3,plain,
% 2.11/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.11/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1980,plain,
% 2.11/1.00      ( ~ r1_tarski(X0,X1)
% 2.11/1.00      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 2.11/1.00      | r1_tarski(k2_relat_1(sK3),X1) ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2172,plain,
% 2.11/1.00      ( r1_tarski(k2_relat_1(sK3),X0)
% 2.11/1.00      | ~ r1_tarski(k2_relat_1(sK3),sK1)
% 2.11/1.00      | ~ r1_tarski(sK1,X0) ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_1980]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2174,plain,
% 2.11/1.00      ( ~ r1_tarski(k2_relat_1(sK3),sK1)
% 2.11/1.00      | r1_tarski(k2_relat_1(sK3),k1_xboole_0)
% 2.11/1.00      | ~ r1_tarski(sK1,k1_xboole_0) ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_2172]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2394,plain,
% 2.11/1.00      ( ~ r1_tarski(k2_relat_1(sK3),sK1)
% 2.11/1.00      | r1_tarski(k2_relat_1(sK3),sK2)
% 2.11/1.00      | ~ r1_tarski(sK1,sK2) ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_2172]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2395,plain,
% 2.11/1.00      ( r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
% 2.11/1.00      | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
% 2.11/1.00      | r1_tarski(sK1,sK2) != iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_2394]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1371,plain,
% 2.11/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.11/1.00      theory(equality) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2397,plain,
% 2.11/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(sK1,X2) | X2 != X1 | sK1 != X0 ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_1371]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2399,plain,
% 2.11/1.00      ( r1_tarski(sK1,k1_xboole_0)
% 2.11/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.11/1.00      | sK1 != k1_xboole_0
% 2.11/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_2397]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_18,plain,
% 2.11/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.11/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.11/1.00      | k1_xboole_0 = X2 ),
% 2.11/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_26,negated_conjecture,
% 2.11/1.00      ( v1_funct_2(sK3,sK0,sK1) ),
% 2.11/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_995,plain,
% 2.11/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.11/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.11/1.00      | sK1 != X2
% 2.11/1.00      | sK0 != X1
% 2.11/1.00      | sK3 != X0
% 2.11/1.00      | k1_xboole_0 = X2 ),
% 2.11/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_996,plain,
% 2.11/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.11/1.00      | k1_relset_1(sK0,sK1,sK3) = sK0
% 2.11/1.00      | k1_xboole_0 = sK1 ),
% 2.11/1.00      inference(unflattening,[status(thm)],[c_995]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_998,plain,
% 2.11/1.00      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 2.11/1.00      inference(global_propositional_subsumption,[status(thm)],[c_996,c_25]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1747,plain,
% 2.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_12,plain,
% 2.11/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.11/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.11/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1749,plain,
% 2.11/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.11/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2287,plain,
% 2.11/1.00      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 2.11/1.00      inference(superposition,[status(thm)],[c_1747,c_1749]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2357,plain,
% 2.11/1.00      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 2.11/1.00      inference(superposition,[status(thm)],[c_998,c_2287]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1746,plain,
% 2.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
% 2.11/1.00      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 2.11/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_307,plain,
% 2.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
% 2.11/1.00      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 2.11/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1923,plain,
% 2.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.11/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1922]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2011,plain,
% 2.11/1.00      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 2.11/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top ),
% 2.11/1.00      inference(global_propositional_subsumption,
% 2.11/1.00                [status(thm)],
% 2.11/1.00                [c_1746,c_30,c_307,c_1923]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2012,plain,
% 2.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
% 2.11/1.00      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 2.11/1.00      inference(renaming,[status(thm)],[c_2011]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2431,plain,
% 2.11/1.00      ( sK1 = k1_xboole_0
% 2.11/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
% 2.11/1.00      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 2.11/1.00      inference(superposition,[status(thm)],[c_2357,c_2012]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_22,negated_conjecture,
% 2.11/1.00      ( ~ v1_funct_2(sK3,sK0,sK2)
% 2.11/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.11/1.00      | ~ v1_funct_1(sK3) ),
% 2.11/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_150,plain,
% 2.11/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.11/1.00      | ~ v1_funct_2(sK3,sK0,sK2) ),
% 2.11/1.00      inference(global_propositional_subsumption,[status(thm)],[c_22,c_27]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_151,negated_conjecture,
% 2.11/1.00      ( ~ v1_funct_2(sK3,sK0,sK2)
% 2.11/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.11/1.00      inference(renaming,[status(thm)],[c_150]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1045,plain,
% 2.11/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.11/1.00      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 2.11/1.00      | ~ v1_relat_1(sK3)
% 2.11/1.00      | k1_relat_1(sK3) != sK0
% 2.11/1.00      | sK2 != X0
% 2.11/1.00      | sK3 != sK3 ),
% 2.11/1.00      inference(resolution_lifted,[status(thm)],[c_151,c_291]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1046,plain,
% 2.11/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.11/1.00      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 2.11/1.00      | ~ v1_relat_1(sK3)
% 2.11/1.00      | k1_relat_1(sK3) != sK0 ),
% 2.11/1.00      inference(unflattening,[status(thm)],[c_1045]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1056,plain,
% 2.11/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.11/1.00      | k1_relat_1(sK3) != sK0 ),
% 2.11/1.00      inference(forward_subsumption_resolution,
% 2.11/1.00                [status(thm)],
% 2.11/1.00                [c_1046,c_9,c_356]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1735,plain,
% 2.11/1.00      ( k1_relat_1(sK3) != sK0
% 2.11/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1056]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2455,plain,
% 2.11/1.00      ( sK1 = k1_xboole_0
% 2.11/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.11/1.00      inference(superposition,[status(thm)],[c_2357,c_1735]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2971,plain,
% 2.11/1.00      ( sK1 = k1_xboole_0 | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 2.11/1.00      inference(superposition,[status(thm)],[c_2431,c_2455]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2994,plain,
% 2.11/1.00      ( k1_xboole_0 = k1_relat_1(sK3) | k1_xboole_0 = sK3 ),
% 2.11/1.00      inference(global_propositional_subsumption,
% 2.11/1.00                [status(thm)],
% 2.11/1.00                [c_1741,c_25,c_30,c_31,c_83,c_89,c_308,c_908,c_1922,c_1932,
% 2.11/1.00                 c_1933,c_2174,c_2395,c_2399,c_2971]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3001,plain,
% 2.11/1.00      ( sK1 = k1_xboole_0 | sK0 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.11/1.00      inference(superposition,[status(thm)],[c_2994,c_2357]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1370,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1947,plain,
% 2.11/1.00      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_1370]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2037,plain,
% 2.11/1.00      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_1947]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1369,plain,( X0 = X0 ),theory(equality) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2038,plain,
% 2.11/1.00      ( sK0 = sK0 ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_1369]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_891,plain,
% 2.11/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.11/1.00      | sK1 != k1_xboole_0
% 2.11/1.00      | sK0 != X1
% 2.11/1.00      | sK3 != X0
% 2.11/1.00      | k1_xboole_0 = X0
% 2.11/1.00      | k1_xboole_0 = X1 ),
% 2.11/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_892,plain,
% 2.11/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 2.11/1.00      | sK1 != k1_xboole_0
% 2.11/1.00      | k1_xboole_0 = sK0
% 2.11/1.00      | k1_xboole_0 = sK3 ),
% 2.11/1.00      inference(unflattening,[status(thm)],[c_891]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1742,plain,
% 2.11/1.00      ( sK1 != k1_xboole_0
% 2.11/1.00      | k1_xboole_0 = sK0
% 2.11/1.00      | k1_xboole_0 = sK3
% 2.11/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_892]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_23,negated_conjecture,
% 2.11/1.00      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 2.11/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2209,plain,
% 2.11/1.00      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_1370]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2210,plain,
% 2.11/1.00      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_2209]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2436,plain,
% 2.11/1.00      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK0 ),
% 2.11/1.00      inference(global_propositional_subsumption,
% 2.11/1.00                [status(thm)],
% 2.11/1.00                [c_1742,c_23,c_83,c_89,c_2210]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3195,plain,
% 2.11/1.00      ( sK0 = k1_xboole_0 ),
% 2.11/1.00      inference(global_propositional_subsumption,
% 2.11/1.00                [status(thm)],
% 2.11/1.00                [c_3001,c_30,c_31,c_1933,c_2037,c_2038,c_2395,c_2436,c_2971]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3201,plain,
% 2.11/1.00      ( k1_relat_1(sK3) != k1_xboole_0
% 2.11/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.11/1.00      inference(demodulation,[status(thm)],[c_3195,c_1735]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3205,plain,
% 2.11/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_relat_1(sK3) ),
% 2.11/1.00      inference(demodulation,[status(thm)],[c_3195,c_2287]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_17,plain,
% 2.11/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.11/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.11/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_947,plain,
% 2.11/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.11/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.11/1.00      | sK1 != X1
% 2.11/1.00      | sK0 != k1_xboole_0
% 2.11/1.00      | sK3 != X0 ),
% 2.11/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_948,plain,
% 2.11/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 2.11/1.00      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 2.11/1.00      | sK0 != k1_xboole_0 ),
% 2.11/1.00      inference(unflattening,[status(thm)],[c_947]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1739,plain,
% 2.11/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 2.11/1.00      | sK0 != k1_xboole_0
% 2.11/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_948]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3208,plain,
% 2.11/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 2.11/1.00      | k1_xboole_0 != k1_xboole_0
% 2.11/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 2.11/1.00      inference(demodulation,[status(thm)],[c_3195,c_1739]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3225,plain,
% 2.11/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 2.11/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 2.11/1.00      inference(equality_resolution_simp,[status(thm)],[c_3208]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3211,plain,
% 2.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 2.11/1.00      inference(demodulation,[status(thm)],[c_3195,c_1747]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3228,plain,
% 2.11/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0 ),
% 2.11/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3225,c_3211]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3239,plain,
% 2.11/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.11/1.00      inference(light_normalisation,[status(thm)],[c_3205,c_3228]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3242,plain,
% 2.11/1.00      ( k1_xboole_0 != k1_xboole_0
% 2.11/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.11/1.00      inference(light_normalisation,[status(thm)],[c_3201,c_3239]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3243,plain,
% 2.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.11/1.00      inference(equality_resolution_simp,[status(thm)],[c_3242]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2969,plain,
% 2.11/1.00      ( k1_relset_1(sK0,X0,sK3) = k1_relat_1(sK3)
% 2.11/1.00      | sK1 = k1_xboole_0
% 2.11/1.00      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 2.11/1.00      inference(superposition,[status(thm)],[c_2431,c_1749]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3429,plain,
% 2.11/1.00      ( sK1 = k1_xboole_0 ),
% 2.11/1.00      inference(global_propositional_subsumption,
% 2.11/1.00                [status(thm)],
% 2.11/1.00                [c_2969,c_30,c_31,c_1933,c_2395,c_2971]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3433,plain,
% 2.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.11/1.00      inference(demodulation,[status(thm)],[c_3429,c_3211]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1744,plain,
% 2.11/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.11/1.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_356]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3579,plain,
% 2.11/1.00      ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) = iProver_top ),
% 2.11/1.00      inference(superposition,[status(thm)],[c_3433,c_1744]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1751,plain,
% 2.11/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1754,plain,
% 2.11/1.00      ( X0 = X1
% 2.11/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.11/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2580,plain,
% 2.11/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.11/1.00      inference(superposition,[status(thm)],[c_1751,c_1754]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3610,plain,
% 2.11/1.00      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 2.11/1.00      inference(superposition,[status(thm)],[c_3579,c_2580]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3524,plain,
% 2.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
% 2.11/1.00      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 2.11/1.00      inference(demodulation,[status(thm)],[c_3239,c_2012]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3674,plain,
% 2.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
% 2.11/1.00      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 2.11/1.00      inference(demodulation,[status(thm)],[c_3610,c_3524]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_82,plain,
% 2.11/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3696,plain,
% 2.11/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
% 2.11/1.00      inference(global_propositional_subsumption,[status(thm)],[c_3674,c_82]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_3790,plain,
% 2.11/1.00      ( $false ),
% 2.11/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3243,c_3696]) ).
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.11/1.00  
% 2.11/1.00  ------                               Statistics
% 2.11/1.00  
% 2.11/1.00  ------ General
% 2.11/1.00  
% 2.11/1.00  abstr_ref_over_cycles:                  0
% 2.11/1.00  abstr_ref_under_cycles:                 0
% 2.11/1.00  gc_basic_clause_elim:                   0
% 2.11/1.00  forced_gc_time:                         0
% 2.11/1.00  parsing_time:                           0.007
% 2.11/1.00  unif_index_cands_time:                  0.
% 2.11/1.00  unif_index_add_time:                    0.
% 2.11/1.00  orderings_time:                         0.
% 2.11/1.00  out_proof_time:                         0.009
% 2.11/1.00  total_time:                             0.135
% 2.11/1.00  num_of_symbols:                         48
% 2.11/1.00  num_of_terms:                           1666
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing
% 2.11/1.00  
% 2.11/1.00  num_of_splits:                          0
% 2.11/1.00  num_of_split_atoms:                     0
% 2.11/1.00  num_of_reused_defs:                     0
% 2.11/1.00  num_eq_ax_congr_red:                    9
% 2.11/1.00  num_of_sem_filtered_clauses:            1
% 2.11/1.00  num_of_subtypes:                        0
% 2.11/1.00  monotx_restored_types:                  0
% 2.11/1.00  sat_num_of_epr_types:                   0
% 2.11/1.00  sat_num_of_non_cyclic_types:            0
% 2.11/1.00  sat_guarded_non_collapsed_types:        0
% 2.11/1.00  num_pure_diseq_elim:                    0
% 2.11/1.00  simp_replaced_by:                       0
% 2.11/1.00  res_preprocessed:                       116
% 2.11/1.00  prep_upred:                             0
% 2.11/1.00  prep_unflattend:                        72
% 2.11/1.00  smt_new_axioms:                         0
% 2.11/1.00  pred_elim_cands:                        3
% 2.11/1.00  pred_elim:                              4
% 2.11/1.00  pred_elim_cl:                           3
% 2.11/1.00  pred_elim_cycles:                       8
% 2.11/1.00  merged_defs:                            0
% 2.11/1.00  merged_defs_ncl:                        0
% 2.11/1.00  bin_hyper_res:                          0
% 2.11/1.00  prep_cycles:                            4
% 2.11/1.00  pred_elim_time:                         0.045
% 2.11/1.00  splitting_time:                         0.
% 2.11/1.00  sem_filter_time:                        0.
% 2.11/1.00  monotx_time:                            0.001
% 2.11/1.00  subtype_inf_time:                       0.
% 2.11/1.00  
% 2.11/1.00  ------ Problem properties
% 2.11/1.00  
% 2.11/1.00  clauses:                                23
% 2.11/1.00  conjectures:                            3
% 2.11/1.00  epr:                                    6
% 2.11/1.00  horn:                                   19
% 2.11/1.00  ground:                                 12
% 2.11/1.00  unary:                                  4
% 2.11/1.00  binary:                                 8
% 2.11/1.00  lits:                                   59
% 2.11/1.00  lits_eq:                                26
% 2.11/1.00  fd_pure:                                0
% 2.11/1.00  fd_pseudo:                              0
% 2.11/1.00  fd_cond:                                1
% 2.11/1.00  fd_pseudo_cond:                         1
% 2.11/1.00  ac_symbols:                             0
% 2.11/1.00  
% 2.11/1.00  ------ Propositional Solver
% 2.11/1.00  
% 2.11/1.00  prop_solver_calls:                      28
% 2.11/1.00  prop_fast_solver_calls:                 919
% 2.11/1.00  smt_solver_calls:                       0
% 2.11/1.00  smt_fast_solver_calls:                  0
% 2.11/1.00  prop_num_of_clauses:                    1031
% 2.11/1.00  prop_preprocess_simplified:             4178
% 2.11/1.00  prop_fo_subsumed:                       25
% 2.11/1.00  prop_solver_time:                       0.
% 2.11/1.00  smt_solver_time:                        0.
% 2.11/1.00  smt_fast_solver_time:                   0.
% 2.11/1.00  prop_fast_solver_time:                  0.
% 2.11/1.00  prop_unsat_core_time:                   0.
% 2.11/1.00  
% 2.11/1.00  ------ QBF
% 2.11/1.00  
% 2.11/1.00  qbf_q_res:                              0
% 2.11/1.00  qbf_num_tautologies:                    0
% 2.11/1.00  qbf_prep_cycles:                        0
% 2.11/1.00  
% 2.11/1.00  ------ BMC1
% 2.11/1.00  
% 2.11/1.00  bmc1_current_bound:                     -1
% 2.11/1.00  bmc1_last_solved_bound:                 -1
% 2.11/1.00  bmc1_unsat_core_size:                   -1
% 2.11/1.00  bmc1_unsat_core_parents_size:           -1
% 2.11/1.00  bmc1_merge_next_fun:                    0
% 2.11/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.11/1.00  
% 2.11/1.00  ------ Instantiation
% 2.11/1.00  
% 2.11/1.00  inst_num_of_clauses:                    321
% 2.11/1.00  inst_num_in_passive:                    107
% 2.11/1.00  inst_num_in_active:                     177
% 2.11/1.00  inst_num_in_unprocessed:                37
% 2.11/1.00  inst_num_of_loops:                      250
% 2.11/1.00  inst_num_of_learning_restarts:          0
% 2.11/1.00  inst_num_moves_active_passive:          70
% 2.11/1.00  inst_lit_activity:                      0
% 2.11/1.00  inst_lit_activity_moves:                0
% 2.11/1.00  inst_num_tautologies:                   0
% 2.11/1.00  inst_num_prop_implied:                  0
% 2.11/1.00  inst_num_existing_simplified:           0
% 2.11/1.00  inst_num_eq_res_simplified:             0
% 2.11/1.00  inst_num_child_elim:                    0
% 2.11/1.00  inst_num_of_dismatching_blockings:      55
% 2.11/1.00  inst_num_of_non_proper_insts:           335
% 2.11/1.00  inst_num_of_duplicates:                 0
% 2.11/1.00  inst_inst_num_from_inst_to_res:         0
% 2.11/1.00  inst_dismatching_checking_time:         0.
% 2.11/1.00  
% 2.11/1.00  ------ Resolution
% 2.11/1.00  
% 2.11/1.00  res_num_of_clauses:                     0
% 2.11/1.00  res_num_in_passive:                     0
% 2.11/1.00  res_num_in_active:                      0
% 2.11/1.00  res_num_of_loops:                       120
% 2.11/1.00  res_forward_subset_subsumed:            32
% 2.11/1.00  res_backward_subset_subsumed:           0
% 2.11/1.00  res_forward_subsumed:                   0
% 2.11/1.00  res_backward_subsumed:                  0
% 2.11/1.00  res_forward_subsumption_resolution:     4
% 2.11/1.00  res_backward_subsumption_resolution:    0
% 2.11/1.00  res_clause_to_clause_subsumption:       206
% 2.11/1.00  res_orphan_elimination:                 0
% 2.11/1.00  res_tautology_del:                      63
% 2.11/1.00  res_num_eq_res_simplified:              1
% 2.11/1.00  res_num_sel_changes:                    0
% 2.11/1.00  res_moves_from_active_to_pass:          0
% 2.11/1.00  
% 2.11/1.00  ------ Superposition
% 2.11/1.00  
% 2.11/1.00  sup_time_total:                         0.
% 2.11/1.00  sup_time_generating:                    0.
% 2.11/1.00  sup_time_sim_full:                      0.
% 2.11/1.00  sup_time_sim_immed:                     0.
% 2.11/1.00  
% 2.11/1.00  sup_num_of_clauses:                     24
% 2.11/1.00  sup_num_in_active:                      19
% 2.11/1.00  sup_num_in_passive:                     5
% 2.11/1.00  sup_num_of_loops:                       49
% 2.11/1.00  sup_fw_superposition:                   23
% 2.11/1.00  sup_bw_superposition:                   29
% 2.11/1.00  sup_immediate_simplified:               25
% 2.11/1.00  sup_given_eliminated:                   1
% 2.11/1.00  comparisons_done:                       0
% 2.11/1.00  comparisons_avoided:                    6
% 2.11/1.00  
% 2.11/1.00  ------ Simplifications
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  sim_fw_subset_subsumed:                 6
% 2.11/1.00  sim_bw_subset_subsumed:                 6
% 2.11/1.00  sim_fw_subsumed:                        4
% 2.11/1.00  sim_bw_subsumed:                        6
% 2.11/1.00  sim_fw_subsumption_res:                 2
% 2.11/1.00  sim_bw_subsumption_res:                 0
% 2.11/1.00  sim_tautology_del:                      4
% 2.11/1.00  sim_eq_tautology_del:                   6
% 2.11/1.00  sim_eq_res_simp:                        3
% 2.11/1.00  sim_fw_demodulated:                     0
% 2.11/1.00  sim_bw_demodulated:                     29
% 2.11/1.00  sim_light_normalised:                   10
% 2.11/1.00  sim_joinable_taut:                      0
% 2.11/1.00  sim_joinable_simp:                      0
% 2.11/1.00  sim_ac_normalised:                      0
% 2.11/1.00  sim_smt_subsumption:                    0
% 2.11/1.00  
%------------------------------------------------------------------------------
