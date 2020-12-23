%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:36 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  264 (6603 expanded)
%              Number of clauses        :  189 (2555 expanded)
%              Number of leaves         :   22 (1188 expanded)
%              Depth                    :   32
%              Number of atoms          :  777 (33263 expanded)
%              Number of equality atoms :  487 (11235 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
        | ~ v1_funct_2(sK4,sK1,sK3)
        | ~ v1_funct_1(sK4) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
      | ~ v1_funct_2(sK4,sK1,sK3)
      | ~ v1_funct_1(sK4) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f37])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f78,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f77])).

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

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f34])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1293,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1283,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1287,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2852,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1283,c_1287])).

cnf(c_30,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1284,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2995,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2852,c_1284])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_32])).

cnf(c_529,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_531,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_529,c_31])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1288,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3461,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1283,c_1288])).

cnf(c_3618,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_531,c_3461])).

cnf(c_17,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1286,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3459,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1286,c_1288])).

cnf(c_13218,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3618,c_3459])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1290,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1291,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2401,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1283,c_1291])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_227,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_228,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_227])).

cnf(c_286,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_228])).

cnf(c_1282,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_2723,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2401,c_1282])).

cnf(c_3139,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_2723])).

cnf(c_13232,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
    | sK2 = k1_xboole_0
    | k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13218,c_3139])).

cnf(c_13233,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13232])).

cnf(c_13240,plain,
    ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
    | sK2 = k1_xboole_0
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2995,c_13233])).

cnf(c_13254,plain,
    ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1293,c_13240])).

cnf(c_25,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_28,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_165,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ v1_funct_2(sK4,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_33])).

cnf(c_166,negated_conjecture,
    ( ~ v1_funct_2(sK4,sK1,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(renaming,[status(thm)],[c_165])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK3 != X2
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_166])).

cnf(c_516,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_1276,plain,
    ( k1_relset_1(sK1,sK3,sK4) != sK1
    | k1_xboole_0 = sK3
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_13259,plain,
    ( k1_relat_1(sK4) != sK1
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13254,c_1276])).

cnf(c_1336,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ r1_tarski(k1_relat_1(sK4),sK1)
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_782,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1452,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_782])).

cnf(c_1891,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2996,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2995])).

cnf(c_3140,plain,
    ( v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3139])).

cnf(c_784,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1478,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK1)
    | X2 != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_1699,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(X1,sK1)
    | X1 != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1478])).

cnf(c_2009,plain,
    ( r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,sK1)
    | X0 != sK1
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1699])).

cnf(c_5208,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1)
    | ~ r1_tarski(sK1,sK1)
    | k1_relat_1(sK4) != sK1
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2009])).

cnf(c_13260,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relat_1(sK4) != sK1
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13259])).

cnf(c_13304,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13259,c_1336,c_1452,c_1891,c_2996,c_3140,c_3618,c_5208,c_13260])).

cnf(c_13305,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_13304])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_13319,plain,
    ( sK3 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13305,c_29])).

cnf(c_3321,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1286,c_1287])).

cnf(c_8519,plain,
    ( k2_relset_1(k1_relat_1(X0),X1,X0) = k2_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1293,c_3321])).

cnf(c_10030,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK3,sK4) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2995,c_8519])).

cnf(c_10137,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK3,sK4) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10030,c_3139])).

cnf(c_13334,plain,
    ( k2_relset_1(k1_relat_1(sK4),k1_xboole_0,sK4) = k2_relat_1(sK4)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13319,c_10137])).

cnf(c_22,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_443,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK1 != X0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_166])).

cnf(c_444,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK3 != k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_1280,plain,
    ( sK3 != k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK1
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1298,plain,
    ( sK3 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1280,c_4])).

cnf(c_91,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_93,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_91])).

cnf(c_96,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_98,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_1771,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | sK4 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1298,c_93,c_98])).

cnf(c_1772,plain,
    ( sK3 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1771])).

cnf(c_13341,plain,
    ( sK1 = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13319,c_1772])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK1 != X1
    | sK4 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_467,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_1279,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_1296,plain,
    ( sK2 != k1_xboole_0
    | sK1 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1279,c_4])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_94,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_95,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_783,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1330,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_783])).

cnf(c_1385,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_1553,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_783])).

cnf(c_1554,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1553])).

cnf(c_1857,plain,
    ( sK2 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1296,c_29,c_94,c_95,c_1385,c_1452,c_1554])).

cnf(c_13348,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | sK1 = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13341])).

cnf(c_13366,plain,
    ( sK4 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13341,c_1336,c_1452,c_1857,c_1891,c_2996,c_3140,c_3618,c_5208,c_13348])).

cnf(c_13367,plain,
    ( sK1 = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_13366])).

cnf(c_13340,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13319,c_2995])).

cnf(c_3320,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1286,c_1291])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1294,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6445,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r1_tarski(k2_zfmisc_1(X0,X1),X2) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3320,c_1294])).

cnf(c_9139,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | r1_tarski(k2_relat_1(X1),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_6445])).

cnf(c_9142,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9139,c_4])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_383,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_384,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_21,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | X1 != X0
    | sK0(X1) != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_384,c_21])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_400,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_3318,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1286])).

cnf(c_3895,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1293,c_3318])).

cnf(c_9241,plain,
    ( r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9142,c_400,c_3895])).

cnf(c_9242,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9241])).

cnf(c_13410,plain,
    ( sK1 = k1_xboole_0
    | sK4 = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_13340,c_9242])).

cnf(c_13475,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13334,c_3139,c_13367,c_13410])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK3 != X1
    | sK1 != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_166])).

cnf(c_487,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_1278,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_1297,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1278,c_5])).

cnf(c_13523,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13475,c_1297])).

cnf(c_13534,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13523])).

cnf(c_13535,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13534,c_5])).

cnf(c_1353,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_1354,plain,
    ( sK1 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1353])).

cnf(c_1356,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_3319,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1286])).

cnf(c_3904,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3618,c_3319])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1406,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1407,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1406])).

cnf(c_1455,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_782])).

cnf(c_1536,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_1537,plain,
    ( k1_xboole_0 = sK1
    | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1536])).

cnf(c_1694,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(X2,X3)
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_783])).

cnf(c_1695,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1694])).

cnf(c_1838,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1839,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1838])).

cnf(c_1841,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1839])).

cnf(c_1589,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1919,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_1920,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1919])).

cnf(c_1597,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,X2)
    | X2 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_2022,plain,
    ( ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,X1)
    | X1 != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1597])).

cnf(c_3332,plain,
    ( r1_tarski(sK4,X0)
    | ~ r1_tarski(sK4,k2_zfmisc_1(X1,X2))
    | X0 != k2_zfmisc_1(X1,X2)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2022])).

cnf(c_3348,plain,
    ( X0 != k2_zfmisc_1(X1,X2)
    | sK4 != sK4
    | r1_tarski(sK4,X0) = iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3332])).

cnf(c_3350,plain,
    ( sK4 != sK4
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3348])).

cnf(c_2779,plain,
    ( r1_tarski(sK4,X0)
    | ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))
    | X0 != k2_zfmisc_1(sK1,sK2)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2022])).

cnf(c_3531,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(X0,X1))
    | ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))
    | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2779])).

cnf(c_3532,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2)
    | sK4 != sK4
    | r1_tarski(sK4,k2_zfmisc_1(X0,X1)) = iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3531])).

cnf(c_3534,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK1,sK2)
    | sK4 != sK4
    | r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3532])).

cnf(c_785,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_4486,plain,
    ( X0 != sK2
    | X1 != sK1
    | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_4487,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK1,sK2)
    | k1_xboole_0 != sK2
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_4486])).

cnf(c_4515,plain,
    ( r1_tarski(sK1,k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3904,c_36,c_94,c_95,c_1407,c_1455,c_1537,c_1554,c_1695,c_1841,c_1920,c_3139,c_3350,c_3534,c_4487])).

cnf(c_4516,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4515])).

cnf(c_4521,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1293,c_4516])).

cnf(c_14157,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13535,c_94,c_95,c_98,c_1356,c_3139,c_4521,c_13367,c_13410])).

cnf(c_13521,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13475,c_2401])).

cnf(c_13536,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13521,c_5])).

cnf(c_1292,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1281,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_2847,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1292,c_1281])).

cnf(c_13754,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13536,c_2847])).

cnf(c_14159,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14157,c_13754])).

cnf(c_18,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1285,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2050,plain,
    ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1285])).

cnf(c_2591,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2050,c_1281])).

cnf(c_13,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2598,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2591,c_13])).

cnf(c_12,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1289,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1983,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1289])).

cnf(c_2649,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2598,c_1983])).

cnf(c_3458,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1292,c_1288])).

cnf(c_7260,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2649,c_3458])).

cnf(c_14,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2597,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2591,c_14])).

cnf(c_7263,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7260,c_2597])).

cnf(c_14160,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14159,c_7263])).

cnf(c_14161,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_14160])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n022.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 19:11:26 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.31  % Running in FOF mode
% 3.64/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/0.97  
% 3.64/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.64/0.97  
% 3.64/0.97  ------  iProver source info
% 3.64/0.97  
% 3.64/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.64/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.64/0.97  git: non_committed_changes: false
% 3.64/0.97  git: last_make_outside_of_git: false
% 3.64/0.97  
% 3.64/0.97  ------ 
% 3.64/0.97  
% 3.64/0.97  ------ Input Options
% 3.64/0.97  
% 3.64/0.97  --out_options                           all
% 3.64/0.97  --tptp_safe_out                         true
% 3.64/0.97  --problem_path                          ""
% 3.64/0.97  --include_path                          ""
% 3.64/0.97  --clausifier                            res/vclausify_rel
% 3.64/0.97  --clausifier_options                    ""
% 3.64/0.97  --stdin                                 false
% 3.64/0.97  --stats_out                             all
% 3.64/0.97  
% 3.64/0.97  ------ General Options
% 3.64/0.97  
% 3.64/0.97  --fof                                   false
% 3.64/0.97  --time_out_real                         305.
% 3.64/0.97  --time_out_virtual                      -1.
% 3.64/0.97  --symbol_type_check                     false
% 3.64/0.97  --clausify_out                          false
% 3.64/0.97  --sig_cnt_out                           false
% 3.64/0.97  --trig_cnt_out                          false
% 3.64/0.97  --trig_cnt_out_tolerance                1.
% 3.64/0.97  --trig_cnt_out_sk_spl                   false
% 3.64/0.97  --abstr_cl_out                          false
% 3.64/0.97  
% 3.64/0.97  ------ Global Options
% 3.64/0.97  
% 3.64/0.97  --schedule                              default
% 3.64/0.97  --add_important_lit                     false
% 3.64/0.97  --prop_solver_per_cl                    1000
% 3.64/0.97  --min_unsat_core                        false
% 3.64/0.97  --soft_assumptions                      false
% 3.64/0.97  --soft_lemma_size                       3
% 3.64/0.97  --prop_impl_unit_size                   0
% 3.64/0.97  --prop_impl_unit                        []
% 3.64/0.97  --share_sel_clauses                     true
% 3.64/0.97  --reset_solvers                         false
% 3.64/0.97  --bc_imp_inh                            [conj_cone]
% 3.64/0.97  --conj_cone_tolerance                   3.
% 3.64/0.97  --extra_neg_conj                        none
% 3.64/0.97  --large_theory_mode                     true
% 3.64/0.97  --prolific_symb_bound                   200
% 3.64/0.97  --lt_threshold                          2000
% 3.64/0.97  --clause_weak_htbl                      true
% 3.64/0.97  --gc_record_bc_elim                     false
% 3.64/0.97  
% 3.64/0.97  ------ Preprocessing Options
% 3.64/0.97  
% 3.64/0.97  --preprocessing_flag                    true
% 3.64/0.97  --time_out_prep_mult                    0.1
% 3.64/0.97  --splitting_mode                        input
% 3.64/0.97  --splitting_grd                         true
% 3.64/0.97  --splitting_cvd                         false
% 3.64/0.97  --splitting_cvd_svl                     false
% 3.64/0.97  --splitting_nvd                         32
% 3.64/0.97  --sub_typing                            true
% 3.64/0.97  --prep_gs_sim                           true
% 3.64/0.97  --prep_unflatten                        true
% 3.64/0.97  --prep_res_sim                          true
% 3.64/0.97  --prep_upred                            true
% 3.64/0.97  --prep_sem_filter                       exhaustive
% 3.64/0.97  --prep_sem_filter_out                   false
% 3.64/0.97  --pred_elim                             true
% 3.64/0.97  --res_sim_input                         true
% 3.64/0.97  --eq_ax_congr_red                       true
% 3.64/0.97  --pure_diseq_elim                       true
% 3.64/0.97  --brand_transform                       false
% 3.64/0.97  --non_eq_to_eq                          false
% 3.64/0.97  --prep_def_merge                        true
% 3.64/0.97  --prep_def_merge_prop_impl              false
% 3.64/0.97  --prep_def_merge_mbd                    true
% 3.64/0.97  --prep_def_merge_tr_red                 false
% 3.64/0.97  --prep_def_merge_tr_cl                  false
% 3.64/0.97  --smt_preprocessing                     true
% 3.64/0.97  --smt_ac_axioms                         fast
% 3.64/0.97  --preprocessed_out                      false
% 3.64/0.97  --preprocessed_stats                    false
% 3.64/0.97  
% 3.64/0.97  ------ Abstraction refinement Options
% 3.64/0.97  
% 3.64/0.97  --abstr_ref                             []
% 3.64/0.97  --abstr_ref_prep                        false
% 3.64/0.97  --abstr_ref_until_sat                   false
% 3.64/0.97  --abstr_ref_sig_restrict                funpre
% 3.64/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.64/0.97  --abstr_ref_under                       []
% 3.64/0.97  
% 3.64/0.97  ------ SAT Options
% 3.64/0.97  
% 3.64/0.97  --sat_mode                              false
% 3.64/0.97  --sat_fm_restart_options                ""
% 3.64/0.97  --sat_gr_def                            false
% 3.64/0.97  --sat_epr_types                         true
% 3.64/0.97  --sat_non_cyclic_types                  false
% 3.64/0.97  --sat_finite_models                     false
% 3.64/0.97  --sat_fm_lemmas                         false
% 3.64/0.97  --sat_fm_prep                           false
% 3.64/0.97  --sat_fm_uc_incr                        true
% 3.64/0.97  --sat_out_model                         small
% 3.64/0.97  --sat_out_clauses                       false
% 3.64/0.97  
% 3.64/0.97  ------ QBF Options
% 3.64/0.97  
% 3.64/0.97  --qbf_mode                              false
% 3.64/0.97  --qbf_elim_univ                         false
% 3.64/0.97  --qbf_dom_inst                          none
% 3.64/0.97  --qbf_dom_pre_inst                      false
% 3.64/0.97  --qbf_sk_in                             false
% 3.64/0.97  --qbf_pred_elim                         true
% 3.64/0.97  --qbf_split                             512
% 3.64/0.97  
% 3.64/0.97  ------ BMC1 Options
% 3.64/0.97  
% 3.64/0.97  --bmc1_incremental                      false
% 3.64/0.97  --bmc1_axioms                           reachable_all
% 3.64/0.97  --bmc1_min_bound                        0
% 3.64/0.97  --bmc1_max_bound                        -1
% 3.64/0.97  --bmc1_max_bound_default                -1
% 3.64/0.97  --bmc1_symbol_reachability              true
% 3.64/0.97  --bmc1_property_lemmas                  false
% 3.64/0.97  --bmc1_k_induction                      false
% 3.64/0.97  --bmc1_non_equiv_states                 false
% 3.64/0.97  --bmc1_deadlock                         false
% 3.64/0.97  --bmc1_ucm                              false
% 3.64/0.97  --bmc1_add_unsat_core                   none
% 3.64/0.97  --bmc1_unsat_core_children              false
% 3.64/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.64/0.97  --bmc1_out_stat                         full
% 3.64/0.97  --bmc1_ground_init                      false
% 3.64/0.97  --bmc1_pre_inst_next_state              false
% 3.64/0.97  --bmc1_pre_inst_state                   false
% 3.64/0.97  --bmc1_pre_inst_reach_state             false
% 3.64/0.97  --bmc1_out_unsat_core                   false
% 3.64/0.97  --bmc1_aig_witness_out                  false
% 3.64/0.97  --bmc1_verbose                          false
% 3.64/0.97  --bmc1_dump_clauses_tptp                false
% 3.64/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.64/0.97  --bmc1_dump_file                        -
% 3.64/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.64/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.64/0.97  --bmc1_ucm_extend_mode                  1
% 3.64/0.97  --bmc1_ucm_init_mode                    2
% 3.64/0.97  --bmc1_ucm_cone_mode                    none
% 3.64/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.64/0.97  --bmc1_ucm_relax_model                  4
% 3.64/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.64/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.64/0.97  --bmc1_ucm_layered_model                none
% 3.64/0.97  --bmc1_ucm_max_lemma_size               10
% 3.64/0.97  
% 3.64/0.97  ------ AIG Options
% 3.64/0.97  
% 3.64/0.97  --aig_mode                              false
% 3.64/0.97  
% 3.64/0.97  ------ Instantiation Options
% 3.64/0.97  
% 3.64/0.97  --instantiation_flag                    true
% 3.64/0.97  --inst_sos_flag                         true
% 3.64/0.97  --inst_sos_phase                        true
% 3.64/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.64/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.64/0.97  --inst_lit_sel_side                     num_symb
% 3.64/0.97  --inst_solver_per_active                1400
% 3.64/0.97  --inst_solver_calls_frac                1.
% 3.64/0.97  --inst_passive_queue_type               priority_queues
% 3.64/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.64/0.97  --inst_passive_queues_freq              [25;2]
% 3.64/0.97  --inst_dismatching                      true
% 3.64/0.97  --inst_eager_unprocessed_to_passive     true
% 3.64/0.97  --inst_prop_sim_given                   true
% 3.64/0.97  --inst_prop_sim_new                     false
% 3.64/0.97  --inst_subs_new                         false
% 3.64/0.97  --inst_eq_res_simp                      false
% 3.64/0.97  --inst_subs_given                       false
% 3.64/0.97  --inst_orphan_elimination               true
% 3.64/0.97  --inst_learning_loop_flag               true
% 3.64/0.97  --inst_learning_start                   3000
% 3.64/0.97  --inst_learning_factor                  2
% 3.64/0.97  --inst_start_prop_sim_after_learn       3
% 3.64/0.97  --inst_sel_renew                        solver
% 3.64/0.97  --inst_lit_activity_flag                true
% 3.64/0.97  --inst_restr_to_given                   false
% 3.64/0.97  --inst_activity_threshold               500
% 3.64/0.97  --inst_out_proof                        true
% 3.64/0.97  
% 3.64/0.97  ------ Resolution Options
% 3.64/0.97  
% 3.64/0.97  --resolution_flag                       true
% 3.64/0.97  --res_lit_sel                           adaptive
% 3.64/0.97  --res_lit_sel_side                      none
% 3.64/0.97  --res_ordering                          kbo
% 3.64/0.97  --res_to_prop_solver                    active
% 3.64/0.97  --res_prop_simpl_new                    false
% 3.64/0.97  --res_prop_simpl_given                  true
% 3.64/0.97  --res_passive_queue_type                priority_queues
% 3.64/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.64/0.97  --res_passive_queues_freq               [15;5]
% 3.64/0.97  --res_forward_subs                      full
% 3.64/0.97  --res_backward_subs                     full
% 3.64/0.97  --res_forward_subs_resolution           true
% 3.64/0.97  --res_backward_subs_resolution          true
% 3.64/0.97  --res_orphan_elimination                true
% 3.64/0.97  --res_time_limit                        2.
% 3.64/0.97  --res_out_proof                         true
% 3.64/0.97  
% 3.64/0.97  ------ Superposition Options
% 3.64/0.97  
% 3.64/0.97  --superposition_flag                    true
% 3.64/0.97  --sup_passive_queue_type                priority_queues
% 3.64/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.64/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.64/0.97  --demod_completeness_check              fast
% 3.64/0.97  --demod_use_ground                      true
% 3.64/0.97  --sup_to_prop_solver                    passive
% 3.64/0.97  --sup_prop_simpl_new                    true
% 3.64/0.97  --sup_prop_simpl_given                  true
% 3.64/0.97  --sup_fun_splitting                     true
% 3.64/0.97  --sup_smt_interval                      50000
% 3.64/0.97  
% 3.64/0.97  ------ Superposition Simplification Setup
% 3.64/0.97  
% 3.64/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.64/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.64/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.64/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.64/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.64/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.64/0.97  --sup_immed_triv                        [TrivRules]
% 3.64/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/0.97  --sup_immed_bw_main                     []
% 3.64/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.64/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.64/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/0.97  --sup_input_bw                          []
% 3.64/0.97  
% 3.64/0.97  ------ Combination Options
% 3.64/0.97  
% 3.64/0.97  --comb_res_mult                         3
% 3.64/0.97  --comb_sup_mult                         2
% 3.64/0.97  --comb_inst_mult                        10
% 3.64/0.97  
% 3.64/0.97  ------ Debug Options
% 3.64/0.97  
% 3.64/0.97  --dbg_backtrace                         false
% 3.64/0.97  --dbg_dump_prop_clauses                 false
% 3.64/0.97  --dbg_dump_prop_clauses_file            -
% 3.64/0.97  --dbg_out_stat                          false
% 3.64/0.97  ------ Parsing...
% 3.64/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.64/0.97  
% 3.64/0.97  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.64/0.97  
% 3.64/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.64/0.97  
% 3.64/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/0.97  ------ Proving...
% 3.64/0.97  ------ Problem Properties 
% 3.64/0.97  
% 3.64/0.97  
% 3.64/0.97  clauses                                 29
% 3.64/0.97  conjectures                             3
% 3.64/0.97  EPR                                     4
% 3.64/0.97  Horn                                    26
% 3.64/0.97  unary                                   10
% 3.64/0.97  binary                                  10
% 3.64/0.97  lits                                    62
% 3.64/0.97  lits eq                                 32
% 3.64/0.97  fd_pure                                 0
% 3.64/0.97  fd_pseudo                               0
% 3.64/0.97  fd_cond                                 4
% 3.64/0.97  fd_pseudo_cond                          1
% 3.64/0.97  AC symbols                              0
% 3.64/0.97  
% 3.64/0.97  ------ Schedule dynamic 5 is on 
% 3.64/0.97  
% 3.64/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.64/0.97  
% 3.64/0.97  
% 3.64/0.97  ------ 
% 3.64/0.97  Current options:
% 3.64/0.97  ------ 
% 3.64/0.97  
% 3.64/0.97  ------ Input Options
% 3.64/0.97  
% 3.64/0.97  --out_options                           all
% 3.64/0.97  --tptp_safe_out                         true
% 3.64/0.97  --problem_path                          ""
% 3.64/0.97  --include_path                          ""
% 3.64/0.97  --clausifier                            res/vclausify_rel
% 3.64/0.97  --clausifier_options                    ""
% 3.64/0.97  --stdin                                 false
% 3.64/0.97  --stats_out                             all
% 3.64/0.97  
% 3.64/0.97  ------ General Options
% 3.64/0.97  
% 3.64/0.97  --fof                                   false
% 3.64/0.97  --time_out_real                         305.
% 3.64/0.97  --time_out_virtual                      -1.
% 3.64/0.97  --symbol_type_check                     false
% 3.64/0.97  --clausify_out                          false
% 3.64/0.97  --sig_cnt_out                           false
% 3.64/0.97  --trig_cnt_out                          false
% 3.64/0.97  --trig_cnt_out_tolerance                1.
% 3.64/0.97  --trig_cnt_out_sk_spl                   false
% 3.64/0.97  --abstr_cl_out                          false
% 3.64/0.97  
% 3.64/0.97  ------ Global Options
% 3.64/0.97  
% 3.64/0.97  --schedule                              default
% 3.64/0.97  --add_important_lit                     false
% 3.64/0.97  --prop_solver_per_cl                    1000
% 3.64/0.97  --min_unsat_core                        false
% 3.64/0.97  --soft_assumptions                      false
% 3.64/0.97  --soft_lemma_size                       3
% 3.64/0.97  --prop_impl_unit_size                   0
% 3.64/0.97  --prop_impl_unit                        []
% 3.64/0.97  --share_sel_clauses                     true
% 3.64/0.97  --reset_solvers                         false
% 3.64/0.97  --bc_imp_inh                            [conj_cone]
% 3.64/0.97  --conj_cone_tolerance                   3.
% 3.64/0.97  --extra_neg_conj                        none
% 3.64/0.97  --large_theory_mode                     true
% 3.64/0.97  --prolific_symb_bound                   200
% 3.64/0.97  --lt_threshold                          2000
% 3.64/0.97  --clause_weak_htbl                      true
% 3.64/0.97  --gc_record_bc_elim                     false
% 3.64/0.97  
% 3.64/0.97  ------ Preprocessing Options
% 3.64/0.97  
% 3.64/0.97  --preprocessing_flag                    true
% 3.64/0.97  --time_out_prep_mult                    0.1
% 3.64/0.97  --splitting_mode                        input
% 3.64/0.97  --splitting_grd                         true
% 3.64/0.97  --splitting_cvd                         false
% 3.64/0.97  --splitting_cvd_svl                     false
% 3.64/0.97  --splitting_nvd                         32
% 3.64/0.97  --sub_typing                            true
% 3.64/0.97  --prep_gs_sim                           true
% 3.64/0.97  --prep_unflatten                        true
% 3.64/0.97  --prep_res_sim                          true
% 3.64/0.97  --prep_upred                            true
% 3.64/0.97  --prep_sem_filter                       exhaustive
% 3.64/0.97  --prep_sem_filter_out                   false
% 3.64/0.97  --pred_elim                             true
% 3.64/0.97  --res_sim_input                         true
% 3.64/0.97  --eq_ax_congr_red                       true
% 3.64/0.97  --pure_diseq_elim                       true
% 3.64/0.97  --brand_transform                       false
% 3.64/0.97  --non_eq_to_eq                          false
% 3.64/0.97  --prep_def_merge                        true
% 3.64/0.97  --prep_def_merge_prop_impl              false
% 3.64/0.97  --prep_def_merge_mbd                    true
% 3.64/0.97  --prep_def_merge_tr_red                 false
% 3.64/0.97  --prep_def_merge_tr_cl                  false
% 3.64/0.97  --smt_preprocessing                     true
% 3.64/0.97  --smt_ac_axioms                         fast
% 3.64/0.97  --preprocessed_out                      false
% 3.64/0.97  --preprocessed_stats                    false
% 3.64/0.97  
% 3.64/0.97  ------ Abstraction refinement Options
% 3.64/0.97  
% 3.64/0.97  --abstr_ref                             []
% 3.64/0.97  --abstr_ref_prep                        false
% 3.64/0.97  --abstr_ref_until_sat                   false
% 3.64/0.97  --abstr_ref_sig_restrict                funpre
% 3.64/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.64/0.97  --abstr_ref_under                       []
% 3.64/0.97  
% 3.64/0.97  ------ SAT Options
% 3.64/0.97  
% 3.64/0.97  --sat_mode                              false
% 3.64/0.97  --sat_fm_restart_options                ""
% 3.64/0.97  --sat_gr_def                            false
% 3.64/0.97  --sat_epr_types                         true
% 3.64/0.97  --sat_non_cyclic_types                  false
% 3.64/0.97  --sat_finite_models                     false
% 3.64/0.97  --sat_fm_lemmas                         false
% 3.64/0.97  --sat_fm_prep                           false
% 3.64/0.97  --sat_fm_uc_incr                        true
% 3.64/0.97  --sat_out_model                         small
% 3.64/0.97  --sat_out_clauses                       false
% 3.64/0.97  
% 3.64/0.97  ------ QBF Options
% 3.64/0.97  
% 3.64/0.97  --qbf_mode                              false
% 3.64/0.97  --qbf_elim_univ                         false
% 3.64/0.97  --qbf_dom_inst                          none
% 3.64/0.97  --qbf_dom_pre_inst                      false
% 3.64/0.97  --qbf_sk_in                             false
% 3.64/0.97  --qbf_pred_elim                         true
% 3.64/0.97  --qbf_split                             512
% 3.64/0.97  
% 3.64/0.97  ------ BMC1 Options
% 3.64/0.97  
% 3.64/0.97  --bmc1_incremental                      false
% 3.64/0.97  --bmc1_axioms                           reachable_all
% 3.64/0.97  --bmc1_min_bound                        0
% 3.64/0.97  --bmc1_max_bound                        -1
% 3.64/0.97  --bmc1_max_bound_default                -1
% 3.64/0.97  --bmc1_symbol_reachability              true
% 3.64/0.97  --bmc1_property_lemmas                  false
% 3.64/0.97  --bmc1_k_induction                      false
% 3.64/0.97  --bmc1_non_equiv_states                 false
% 3.64/0.97  --bmc1_deadlock                         false
% 3.64/0.97  --bmc1_ucm                              false
% 3.64/0.97  --bmc1_add_unsat_core                   none
% 3.64/0.97  --bmc1_unsat_core_children              false
% 3.64/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.64/0.97  --bmc1_out_stat                         full
% 3.64/0.97  --bmc1_ground_init                      false
% 3.64/0.97  --bmc1_pre_inst_next_state              false
% 3.64/0.97  --bmc1_pre_inst_state                   false
% 3.64/0.97  --bmc1_pre_inst_reach_state             false
% 3.64/0.97  --bmc1_out_unsat_core                   false
% 3.64/0.97  --bmc1_aig_witness_out                  false
% 3.64/0.97  --bmc1_verbose                          false
% 3.64/0.97  --bmc1_dump_clauses_tptp                false
% 3.64/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.64/0.97  --bmc1_dump_file                        -
% 3.64/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.64/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.64/0.97  --bmc1_ucm_extend_mode                  1
% 3.64/0.97  --bmc1_ucm_init_mode                    2
% 3.64/0.97  --bmc1_ucm_cone_mode                    none
% 3.64/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.64/0.97  --bmc1_ucm_relax_model                  4
% 3.64/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.64/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.64/0.97  --bmc1_ucm_layered_model                none
% 3.64/0.97  --bmc1_ucm_max_lemma_size               10
% 3.64/0.97  
% 3.64/0.97  ------ AIG Options
% 3.64/0.97  
% 3.64/0.97  --aig_mode                              false
% 3.64/0.97  
% 3.64/0.97  ------ Instantiation Options
% 3.64/0.97  
% 3.64/0.97  --instantiation_flag                    true
% 3.64/0.97  --inst_sos_flag                         true
% 3.64/0.97  --inst_sos_phase                        true
% 3.64/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.64/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.64/0.97  --inst_lit_sel_side                     none
% 3.64/0.97  --inst_solver_per_active                1400
% 3.64/0.97  --inst_solver_calls_frac                1.
% 3.64/0.97  --inst_passive_queue_type               priority_queues
% 3.64/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.64/0.97  --inst_passive_queues_freq              [25;2]
% 3.64/0.97  --inst_dismatching                      true
% 3.64/0.97  --inst_eager_unprocessed_to_passive     true
% 3.64/0.97  --inst_prop_sim_given                   true
% 3.64/0.97  --inst_prop_sim_new                     false
% 3.64/0.97  --inst_subs_new                         false
% 3.64/0.97  --inst_eq_res_simp                      false
% 3.64/0.97  --inst_subs_given                       false
% 3.64/0.97  --inst_orphan_elimination               true
% 3.64/0.97  --inst_learning_loop_flag               true
% 3.64/0.97  --inst_learning_start                   3000
% 3.64/0.97  --inst_learning_factor                  2
% 3.64/0.97  --inst_start_prop_sim_after_learn       3
% 3.64/0.97  --inst_sel_renew                        solver
% 3.64/0.97  --inst_lit_activity_flag                true
% 3.64/0.97  --inst_restr_to_given                   false
% 3.64/0.97  --inst_activity_threshold               500
% 3.64/0.97  --inst_out_proof                        true
% 3.64/0.97  
% 3.64/0.97  ------ Resolution Options
% 3.64/0.97  
% 3.64/0.97  --resolution_flag                       false
% 3.64/0.97  --res_lit_sel                           adaptive
% 3.64/0.97  --res_lit_sel_side                      none
% 3.64/0.97  --res_ordering                          kbo
% 3.64/0.97  --res_to_prop_solver                    active
% 3.64/0.97  --res_prop_simpl_new                    false
% 3.64/0.97  --res_prop_simpl_given                  true
% 3.64/0.97  --res_passive_queue_type                priority_queues
% 3.64/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.64/0.97  --res_passive_queues_freq               [15;5]
% 3.64/0.97  --res_forward_subs                      full
% 3.64/0.97  --res_backward_subs                     full
% 3.64/0.97  --res_forward_subs_resolution           true
% 3.64/0.97  --res_backward_subs_resolution          true
% 3.64/0.97  --res_orphan_elimination                true
% 3.64/0.97  --res_time_limit                        2.
% 3.64/0.97  --res_out_proof                         true
% 3.64/0.97  
% 3.64/0.97  ------ Superposition Options
% 3.64/0.97  
% 3.64/0.97  --superposition_flag                    true
% 3.64/0.97  --sup_passive_queue_type                priority_queues
% 3.64/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.64/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.64/0.97  --demod_completeness_check              fast
% 3.64/0.97  --demod_use_ground                      true
% 3.64/0.97  --sup_to_prop_solver                    passive
% 3.64/0.97  --sup_prop_simpl_new                    true
% 3.64/0.97  --sup_prop_simpl_given                  true
% 3.64/0.97  --sup_fun_splitting                     true
% 3.64/0.97  --sup_smt_interval                      50000
% 3.64/0.97  
% 3.64/0.97  ------ Superposition Simplification Setup
% 3.64/0.97  
% 3.64/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.64/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.64/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.64/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.64/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.64/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.64/0.97  --sup_immed_triv                        [TrivRules]
% 3.64/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/0.97  --sup_immed_bw_main                     []
% 3.64/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.64/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.64/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/0.97  --sup_input_bw                          []
% 3.64/0.97  
% 3.64/0.97  ------ Combination Options
% 3.64/0.97  
% 3.64/0.97  --comb_res_mult                         3
% 3.64/0.97  --comb_sup_mult                         2
% 3.64/0.97  --comb_inst_mult                        10
% 3.64/0.97  
% 3.64/0.97  ------ Debug Options
% 3.64/0.97  
% 3.64/0.97  --dbg_backtrace                         false
% 3.64/0.97  --dbg_dump_prop_clauses                 false
% 3.64/0.97  --dbg_dump_prop_clauses_file            -
% 3.64/0.97  --dbg_out_stat                          false
% 3.64/0.97  
% 3.64/0.97  
% 3.64/0.97  
% 3.64/0.97  
% 3.64/0.97  ------ Proving...
% 3.64/0.97  
% 3.64/0.97  
% 3.64/0.97  % SZS status Theorem for theBenchmark.p
% 3.64/0.97  
% 3.64/0.97   Resolution empty clause
% 3.64/0.97  
% 3.64/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.64/0.97  
% 3.64/0.97  fof(f2,axiom,(
% 3.64/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.64/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.97  
% 3.64/0.97  fof(f29,plain,(
% 3.64/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.64/0.97    inference(nnf_transformation,[],[f2])).
% 3.64/0.97  
% 3.64/0.97  fof(f30,plain,(
% 3.64/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.64/0.97    inference(flattening,[],[f29])).
% 3.64/0.97  
% 3.64/0.97  fof(f40,plain,(
% 3.64/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.64/0.97    inference(cnf_transformation,[],[f30])).
% 3.64/0.97  
% 3.64/0.97  fof(f74,plain,(
% 3.64/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.64/0.97    inference(equality_resolution,[],[f40])).
% 3.64/0.97  
% 3.64/0.97  fof(f16,conjecture,(
% 3.64/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.64/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.97  
% 3.64/0.97  fof(f17,negated_conjecture,(
% 3.64/0.97    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.64/0.97    inference(negated_conjecture,[],[f16])).
% 3.64/0.97  
% 3.64/0.97  fof(f27,plain,(
% 3.64/0.97    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.64/0.97    inference(ennf_transformation,[],[f17])).
% 3.64/0.97  
% 3.64/0.97  fof(f28,plain,(
% 3.64/0.97    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.64/0.97    inference(flattening,[],[f27])).
% 3.64/0.97  
% 3.64/0.97  fof(f37,plain,(
% 3.64/0.97    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 3.64/0.97    introduced(choice_axiom,[])).
% 3.64/0.97  
% 3.64/0.97  fof(f38,plain,(
% 3.64/0.97    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 3.64/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f37])).
% 3.64/0.97  
% 3.64/0.97  fof(f69,plain,(
% 3.64/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.64/0.97    inference(cnf_transformation,[],[f38])).
% 3.64/0.97  
% 3.64/0.97  fof(f11,axiom,(
% 3.64/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.64/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.97  
% 3.64/0.97  fof(f21,plain,(
% 3.64/0.97    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.64/0.97    inference(ennf_transformation,[],[f11])).
% 3.64/0.97  
% 3.64/0.97  fof(f55,plain,(
% 3.64/0.97    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.64/0.97    inference(cnf_transformation,[],[f21])).
% 3.64/0.97  
% 3.64/0.97  fof(f70,plain,(
% 3.64/0.97    r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3)),
% 3.64/0.97    inference(cnf_transformation,[],[f38])).
% 3.64/0.97  
% 3.64/0.97  fof(f15,axiom,(
% 3.64/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.64/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.97  
% 3.64/0.97  fof(f25,plain,(
% 3.64/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.64/0.97    inference(ennf_transformation,[],[f15])).
% 3.64/0.97  
% 3.64/0.97  fof(f26,plain,(
% 3.64/0.97    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.64/0.97    inference(flattening,[],[f25])).
% 3.64/0.97  
% 3.64/0.97  fof(f36,plain,(
% 3.64/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.64/0.97    inference(nnf_transformation,[],[f26])).
% 3.64/0.97  
% 3.64/0.97  fof(f61,plain,(
% 3.64/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.64/0.97    inference(cnf_transformation,[],[f36])).
% 3.64/0.97  
% 3.64/0.97  fof(f68,plain,(
% 3.64/0.97    v1_funct_2(sK4,sK1,sK2)),
% 3.64/0.97    inference(cnf_transformation,[],[f38])).
% 3.64/0.97  
% 3.64/0.97  fof(f10,axiom,(
% 3.64/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.64/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.97  
% 3.64/0.97  fof(f20,plain,(
% 3.64/0.97    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.64/0.97    inference(ennf_transformation,[],[f10])).
% 3.64/0.97  
% 3.64/0.97  fof(f54,plain,(
% 3.64/0.97    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.64/0.97    inference(cnf_transformation,[],[f20])).
% 3.64/0.97  
% 3.64/0.97  fof(f12,axiom,(
% 3.64/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.64/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.97  
% 3.64/0.97  fof(f22,plain,(
% 3.64/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.64/0.97    inference(ennf_transformation,[],[f12])).
% 3.64/0.97  
% 3.64/0.97  fof(f23,plain,(
% 3.64/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.64/0.97    inference(flattening,[],[f22])).
% 3.64/0.97  
% 3.64/0.97  fof(f56,plain,(
% 3.64/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.64/0.97    inference(cnf_transformation,[],[f23])).
% 3.64/0.97  
% 3.64/0.97  fof(f7,axiom,(
% 3.64/0.97    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.64/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.97  
% 3.64/0.97  fof(f50,plain,(
% 3.64/0.97    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.64/0.97    inference(cnf_transformation,[],[f7])).
% 3.64/0.97  
% 3.64/0.97  fof(f4,axiom,(
% 3.64/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.64/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.97  
% 3.64/0.97  fof(f33,plain,(
% 3.64/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.64/0.97    inference(nnf_transformation,[],[f4])).
% 3.64/0.97  
% 3.64/0.97  fof(f46,plain,(
% 3.64/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.64/0.97    inference(cnf_transformation,[],[f33])).
% 3.64/0.97  
% 3.64/0.97  fof(f6,axiom,(
% 3.64/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.64/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.97  
% 3.64/0.97  fof(f19,plain,(
% 3.64/0.97    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.64/0.97    inference(ennf_transformation,[],[f6])).
% 3.64/0.97  
% 3.64/0.97  fof(f49,plain,(
% 3.64/0.97    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.64/0.97    inference(cnf_transformation,[],[f19])).
% 3.64/0.97  
% 3.64/0.97  fof(f47,plain,(
% 3.64/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.64/0.97    inference(cnf_transformation,[],[f33])).
% 3.64/0.97  
% 3.64/0.97  fof(f63,plain,(
% 3.64/0.97    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.64/0.97    inference(cnf_transformation,[],[f36])).
% 3.64/0.97  
% 3.64/0.97  fof(f72,plain,(
% 3.64/0.97    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~v1_funct_2(sK4,sK1,sK3) | ~v1_funct_1(sK4)),
% 3.64/0.97    inference(cnf_transformation,[],[f38])).
% 3.64/0.97  
% 3.64/0.97  fof(f67,plain,(
% 3.64/0.97    v1_funct_1(sK4)),
% 3.64/0.97    inference(cnf_transformation,[],[f38])).
% 3.64/0.97  
% 3.64/0.97  fof(f71,plain,(
% 3.64/0.97    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 3.64/0.97    inference(cnf_transformation,[],[f38])).
% 3.64/0.97  
% 3.64/0.97  fof(f66,plain,(
% 3.64/0.97    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.64/0.97    inference(cnf_transformation,[],[f36])).
% 3.64/0.97  
% 3.64/0.97  fof(f77,plain,(
% 3.64/0.97    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.64/0.97    inference(equality_resolution,[],[f66])).
% 3.64/0.97  
% 3.64/0.97  fof(f78,plain,(
% 3.64/0.97    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.64/0.97    inference(equality_resolution,[],[f77])).
% 3.64/0.97  
% 3.64/0.97  fof(f3,axiom,(
% 3.64/0.97    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.64/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.97  
% 3.64/0.97  fof(f31,plain,(
% 3.64/0.97    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.64/0.97    inference(nnf_transformation,[],[f3])).
% 3.64/0.97  
% 3.64/0.97  fof(f32,plain,(
% 3.64/0.97    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.64/0.97    inference(flattening,[],[f31])).
% 3.64/0.97  
% 3.64/0.97  fof(f45,plain,(
% 3.64/0.97    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.64/0.97    inference(cnf_transformation,[],[f32])).
% 3.64/0.97  
% 3.64/0.97  fof(f75,plain,(
% 3.64/0.97    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.64/0.97    inference(equality_resolution,[],[f45])).
% 3.64/0.97  
% 3.64/0.97  fof(f65,plain,(
% 3.64/0.97    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.64/0.97    inference(cnf_transformation,[],[f36])).
% 3.64/0.97  
% 3.64/0.97  fof(f79,plain,(
% 3.64/0.97    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.64/0.97    inference(equality_resolution,[],[f65])).
% 3.64/0.97  
% 3.64/0.97  fof(f43,plain,(
% 3.64/0.97    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.64/0.97    inference(cnf_transformation,[],[f32])).
% 3.64/0.97  
% 3.64/0.97  fof(f44,plain,(
% 3.64/0.97    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.64/0.97    inference(cnf_transformation,[],[f32])).
% 3.64/0.97  
% 3.64/0.97  fof(f76,plain,(
% 3.64/0.97    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.64/0.97    inference(equality_resolution,[],[f44])).
% 3.64/0.97  
% 3.64/0.97  fof(f42,plain,(
% 3.64/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.64/0.97    inference(cnf_transformation,[],[f30])).
% 3.64/0.97  
% 3.64/0.97  fof(f1,axiom,(
% 3.64/0.97    v1_xboole_0(k1_xboole_0)),
% 3.64/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.97  
% 3.64/0.97  fof(f39,plain,(
% 3.64/0.97    v1_xboole_0(k1_xboole_0)),
% 3.64/0.97    inference(cnf_transformation,[],[f1])).
% 3.64/0.97  
% 3.64/0.97  fof(f5,axiom,(
% 3.64/0.97    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.64/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.97  
% 3.64/0.97  fof(f18,plain,(
% 3.64/0.97    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.64/0.97    inference(ennf_transformation,[],[f5])).
% 3.64/0.97  
% 3.64/0.97  fof(f48,plain,(
% 3.64/0.97    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.64/0.97    inference(cnf_transformation,[],[f18])).
% 3.64/0.97  
% 3.64/0.97  fof(f14,axiom,(
% 3.64/0.97    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.64/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.97  
% 3.64/0.97  fof(f24,plain,(
% 3.64/0.97    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.64/0.97    inference(ennf_transformation,[],[f14])).
% 3.64/0.97  
% 3.64/0.97  fof(f34,plain,(
% 3.64/0.97    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 3.64/0.97    introduced(choice_axiom,[])).
% 3.64/0.97  
% 3.64/0.97  fof(f35,plain,(
% 3.64/0.97    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 3.64/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f34])).
% 3.64/0.97  
% 3.64/0.97  fof(f58,plain,(
% 3.64/0.97    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.64/0.97    inference(cnf_transformation,[],[f35])).
% 3.64/0.97  
% 3.64/0.97  fof(f64,plain,(
% 3.64/0.97    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.64/0.97    inference(cnf_transformation,[],[f36])).
% 3.64/0.97  
% 3.64/0.97  fof(f80,plain,(
% 3.64/0.97    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.64/0.97    inference(equality_resolution,[],[f64])).
% 3.64/0.97  
% 3.64/0.97  fof(f13,axiom,(
% 3.64/0.97    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.64/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.97  
% 3.64/0.97  fof(f57,plain,(
% 3.64/0.97    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.64/0.97    inference(cnf_transformation,[],[f13])).
% 3.64/0.97  
% 3.64/0.97  fof(f9,axiom,(
% 3.64/0.97    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.64/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.97  
% 3.64/0.97  fof(f53,plain,(
% 3.64/0.97    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.64/0.97    inference(cnf_transformation,[],[f9])).
% 3.64/0.97  
% 3.64/0.97  fof(f8,axiom,(
% 3.64/0.97    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 3.64/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.97  
% 3.64/0.97  fof(f51,plain,(
% 3.64/0.97    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 3.64/0.97    inference(cnf_transformation,[],[f8])).
% 3.64/0.97  
% 3.64/0.97  fof(f52,plain,(
% 3.64/0.97    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.64/0.97    inference(cnf_transformation,[],[f9])).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f74]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1293,plain,
% 3.64/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_31,negated_conjecture,
% 3.64/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.64/0.97      inference(cnf_transformation,[],[f69]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1283,plain,
% 3.64/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_16,plain,
% 3.64/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.64/0.97      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.64/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1287,plain,
% 3.64/0.97      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.64/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_2852,plain,
% 3.64/0.97      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_1283,c_1287]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_30,negated_conjecture,
% 3.64/0.97      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) ),
% 3.64/0.97      inference(cnf_transformation,[],[f70]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1284,plain,
% 3.64/0.97      ( r1_tarski(k2_relset_1(sK1,sK2,sK4),sK3) = iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_2995,plain,
% 3.64/0.97      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 3.64/0.97      inference(demodulation,[status(thm)],[c_2852,c_1284]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_27,plain,
% 3.64/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 3.64/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.64/0.97      | k1_relset_1(X1,X2,X0) = X1
% 3.64/0.97      | k1_xboole_0 = X2 ),
% 3.64/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_32,negated_conjecture,
% 3.64/0.97      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.64/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_528,plain,
% 3.64/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.64/0.97      | k1_relset_1(X1,X2,X0) = X1
% 3.64/0.97      | sK2 != X2
% 3.64/0.97      | sK1 != X1
% 3.64/0.97      | sK4 != X0
% 3.64/0.97      | k1_xboole_0 = X2 ),
% 3.64/0.97      inference(resolution_lifted,[status(thm)],[c_27,c_32]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_529,plain,
% 3.64/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.64/0.97      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.64/0.97      | k1_xboole_0 = sK2 ),
% 3.64/0.97      inference(unflattening,[status(thm)],[c_528]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_531,plain,
% 3.64/0.97      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 3.64/0.97      inference(global_propositional_subsumption,[status(thm)],[c_529,c_31]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_15,plain,
% 3.64/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.64/0.97      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.64/0.97      inference(cnf_transformation,[],[f54]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1288,plain,
% 3.64/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.64/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3461,plain,
% 3.64/0.97      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_1283,c_1288]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3618,plain,
% 3.64/0.97      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_531,c_3461]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_17,plain,
% 3.64/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.64/0.97      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.64/0.97      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.64/0.97      | ~ v1_relat_1(X0) ),
% 3.64/0.97      inference(cnf_transformation,[],[f56]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1286,plain,
% 3.64/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.64/0.97      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.64/0.97      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.64/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3459,plain,
% 3.64/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.64/0.97      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.64/0.97      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.64/0.97      | v1_relat_1(X2) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_1286,c_1288]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13218,plain,
% 3.64/0.97      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 3.64/0.97      | sK2 = k1_xboole_0
% 3.64/0.97      | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
% 3.64/0.97      | r1_tarski(sK1,X0) != iProver_top
% 3.64/0.97      | v1_relat_1(sK4) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_3618,c_3459]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_11,plain,
% 3.64/0.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.64/0.97      inference(cnf_transformation,[],[f50]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1290,plain,
% 3.64/0.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_8,plain,
% 3.64/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.64/0.97      inference(cnf_transformation,[],[f46]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1291,plain,
% 3.64/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.64/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_2401,plain,
% 3.64/0.97      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_1283,c_1291]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_10,plain,
% 3.64/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.64/0.97      inference(cnf_transformation,[],[f49]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_7,plain,
% 3.64/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.64/0.97      inference(cnf_transformation,[],[f47]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_227,plain,
% 3.64/0.97      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.64/0.97      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_228,plain,
% 3.64/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.64/0.97      inference(renaming,[status(thm)],[c_227]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_286,plain,
% 3.64/0.97      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.64/0.97      inference(bin_hyper_res,[status(thm)],[c_10,c_228]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1282,plain,
% 3.64/0.97      ( r1_tarski(X0,X1) != iProver_top
% 3.64/0.97      | v1_relat_1(X1) != iProver_top
% 3.64/0.97      | v1_relat_1(X0) = iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_2723,plain,
% 3.64/0.97      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.64/0.97      | v1_relat_1(sK4) = iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_2401,c_1282]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3139,plain,
% 3.64/0.97      ( v1_relat_1(sK4) = iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_1290,c_2723]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13232,plain,
% 3.64/0.97      ( r1_tarski(sK1,X0) != iProver_top
% 3.64/0.97      | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
% 3.64/0.97      | sK2 = k1_xboole_0
% 3.64/0.97      | k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4) ),
% 3.64/0.97      inference(global_propositional_subsumption,
% 3.64/0.97                [status(thm)],
% 3.64/0.97                [c_13218,c_3139]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13233,plain,
% 3.64/0.97      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 3.64/0.97      | sK2 = k1_xboole_0
% 3.64/0.97      | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
% 3.64/0.97      | r1_tarski(sK1,X0) != iProver_top ),
% 3.64/0.97      inference(renaming,[status(thm)],[c_13232]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13240,plain,
% 3.64/0.97      ( k1_relset_1(X0,sK3,sK4) = k1_relat_1(sK4)
% 3.64/0.97      | sK2 = k1_xboole_0
% 3.64/0.97      | r1_tarski(sK1,X0) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_2995,c_13233]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13254,plain,
% 3.64/0.97      ( k1_relset_1(sK1,sK3,sK4) = k1_relat_1(sK4) | sK2 = k1_xboole_0 ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_1293,c_13240]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_25,plain,
% 3.64/0.97      ( v1_funct_2(X0,X1,X2)
% 3.64/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.64/0.97      | k1_relset_1(X1,X2,X0) != X1
% 3.64/0.97      | k1_xboole_0 = X2 ),
% 3.64/0.97      inference(cnf_transformation,[],[f63]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_28,negated_conjecture,
% 3.64/0.97      ( ~ v1_funct_2(sK4,sK1,sK3)
% 3.64/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.64/0.97      | ~ v1_funct_1(sK4) ),
% 3.64/0.97      inference(cnf_transformation,[],[f72]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_33,negated_conjecture,
% 3.64/0.97      ( v1_funct_1(sK4) ),
% 3.64/0.97      inference(cnf_transformation,[],[f67]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_165,plain,
% 3.64/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.64/0.97      | ~ v1_funct_2(sK4,sK1,sK3) ),
% 3.64/0.97      inference(global_propositional_subsumption,[status(thm)],[c_28,c_33]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_166,negated_conjecture,
% 3.64/0.97      ( ~ v1_funct_2(sK4,sK1,sK3)
% 3.64/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 3.64/0.97      inference(renaming,[status(thm)],[c_165]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_515,plain,
% 3.64/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.64/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.64/0.97      | k1_relset_1(X1,X2,X0) != X1
% 3.64/0.97      | sK3 != X2
% 3.64/0.97      | sK1 != X1
% 3.64/0.97      | sK4 != X0
% 3.64/0.97      | k1_xboole_0 = X2 ),
% 3.64/0.97      inference(resolution_lifted,[status(thm)],[c_25,c_166]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_516,plain,
% 3.64/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.64/0.97      | k1_relset_1(sK1,sK3,sK4) != sK1
% 3.64/0.97      | k1_xboole_0 = sK3 ),
% 3.64/0.97      inference(unflattening,[status(thm)],[c_515]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1276,plain,
% 3.64/0.97      ( k1_relset_1(sK1,sK3,sK4) != sK1
% 3.64/0.97      | k1_xboole_0 = sK3
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13259,plain,
% 3.64/0.97      ( k1_relat_1(sK4) != sK1
% 3.64/0.97      | sK2 = k1_xboole_0
% 3.64/0.97      | sK3 = k1_xboole_0
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_13254,c_1276]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1336,plain,
% 3.64/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.64/0.97      | ~ r1_tarski(k1_relat_1(sK4),sK1)
% 3.64/0.97      | ~ r1_tarski(k2_relat_1(sK4),sK3)
% 3.64/0.97      | ~ v1_relat_1(sK4) ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_17]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_782,plain,( X0 = X0 ),theory(equality) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1452,plain,
% 3.64/0.97      ( sK1 = sK1 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_782]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1891,plain,
% 3.64/0.97      ( r1_tarski(sK1,sK1) ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_2996,plain,
% 3.64/0.97      ( r1_tarski(k2_relat_1(sK4),sK3) ),
% 3.64/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_2995]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3140,plain,
% 3.64/0.97      ( v1_relat_1(sK4) ),
% 3.64/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_3139]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_784,plain,
% 3.64/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.64/0.97      theory(equality) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1478,plain,
% 3.64/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK1) | X2 != X0 | sK1 != X1 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_784]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1699,plain,
% 3.64/0.97      ( ~ r1_tarski(X0,sK1) | r1_tarski(X1,sK1) | X1 != X0 | sK1 != sK1 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_1478]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_2009,plain,
% 3.64/0.97      ( r1_tarski(X0,sK1) | ~ r1_tarski(sK1,sK1) | X0 != sK1 | sK1 != sK1 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_1699]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_5208,plain,
% 3.64/0.97      ( r1_tarski(k1_relat_1(sK4),sK1)
% 3.64/0.97      | ~ r1_tarski(sK1,sK1)
% 3.64/0.97      | k1_relat_1(sK4) != sK1
% 3.64/0.97      | sK1 != sK1 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_2009]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13260,plain,
% 3.64/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.64/0.97      | k1_relat_1(sK4) != sK1
% 3.64/0.97      | sK2 = k1_xboole_0
% 3.64/0.97      | sK3 = k1_xboole_0 ),
% 3.64/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_13259]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13304,plain,
% 3.64/0.97      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.64/0.97      inference(global_propositional_subsumption,
% 3.64/0.97                [status(thm)],
% 3.64/0.97                [c_13259,c_1336,c_1452,c_1891,c_2996,c_3140,c_3618,c_5208,
% 3.64/0.97                 c_13260]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13305,plain,
% 3.64/0.97      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.64/0.97      inference(renaming,[status(thm)],[c_13304]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_29,negated_conjecture,
% 3.64/0.97      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 3.64/0.97      inference(cnf_transformation,[],[f71]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13319,plain,
% 3.64/0.97      ( sK3 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_13305,c_29]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3321,plain,
% 3.64/0.97      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.64/0.97      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.64/0.97      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.64/0.97      | v1_relat_1(X2) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_1286,c_1287]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_8519,plain,
% 3.64/0.97      ( k2_relset_1(k1_relat_1(X0),X1,X0) = k2_relat_1(X0)
% 3.64/0.97      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.64/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_1293,c_3321]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_10030,plain,
% 3.64/0.97      ( k2_relset_1(k1_relat_1(sK4),sK3,sK4) = k2_relat_1(sK4)
% 3.64/0.97      | v1_relat_1(sK4) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_2995,c_8519]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_10137,plain,
% 3.64/0.97      ( k2_relset_1(k1_relat_1(sK4),sK3,sK4) = k2_relat_1(sK4) ),
% 3.64/0.97      inference(global_propositional_subsumption,
% 3.64/0.97                [status(thm)],
% 3.64/0.97                [c_10030,c_3139]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13334,plain,
% 3.64/0.97      ( k2_relset_1(k1_relat_1(sK4),k1_xboole_0,sK4) = k2_relat_1(sK4)
% 3.64/0.97      | sK1 = k1_xboole_0 ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_13319,c_10137]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_22,plain,
% 3.64/0.97      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.64/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.64/0.97      | k1_xboole_0 = X0 ),
% 3.64/0.97      inference(cnf_transformation,[],[f78]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_443,plain,
% 3.64/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.64/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.64/0.97      | sK3 != k1_xboole_0
% 3.64/0.97      | sK1 != X0
% 3.64/0.97      | sK4 != k1_xboole_0
% 3.64/0.97      | k1_xboole_0 = X0 ),
% 3.64/0.97      inference(resolution_lifted,[status(thm)],[c_22,c_166]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_444,plain,
% 3.64/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.64/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 3.64/0.97      | sK3 != k1_xboole_0
% 3.64/0.97      | sK4 != k1_xboole_0
% 3.64/0.97      | k1_xboole_0 = sK1 ),
% 3.64/0.97      inference(unflattening,[status(thm)],[c_443]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1280,plain,
% 3.64/0.97      ( sK3 != k1_xboole_0
% 3.64/0.97      | sK4 != k1_xboole_0
% 3.64/0.97      | k1_xboole_0 = sK1
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.64/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_4,plain,
% 3.64/0.97      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.64/0.97      inference(cnf_transformation,[],[f75]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1298,plain,
% 3.64/0.97      ( sK3 != k1_xboole_0
% 3.64/0.97      | sK1 = k1_xboole_0
% 3.64/0.97      | sK4 != k1_xboole_0
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.64/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.64/0.97      inference(demodulation,[status(thm)],[c_1280,c_4]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_91,plain,
% 3.64/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.64/0.97      | r1_tarski(X0,X1) != iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_93,plain,
% 3.64/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.64/0.97      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_91]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_96,plain,
% 3.64/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_98,plain,
% 3.64/0.97      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_96]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1771,plain,
% 3.64/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.64/0.97      | sK4 != k1_xboole_0
% 3.64/0.97      | sK1 = k1_xboole_0
% 3.64/0.97      | sK3 != k1_xboole_0 ),
% 3.64/0.97      inference(global_propositional_subsumption,
% 3.64/0.97                [status(thm)],
% 3.64/0.97                [c_1298,c_93,c_98]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1772,plain,
% 3.64/0.97      ( sK3 != k1_xboole_0
% 3.64/0.97      | sK1 = k1_xboole_0
% 3.64/0.97      | sK4 != k1_xboole_0
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.64/0.97      inference(renaming,[status(thm)],[c_1771]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13341,plain,
% 3.64/0.97      ( sK1 = k1_xboole_0
% 3.64/0.97      | sK4 != k1_xboole_0
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_13319,c_1772]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_23,plain,
% 3.64/0.97      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.64/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.64/0.97      | k1_xboole_0 = X1
% 3.64/0.97      | k1_xboole_0 = X0 ),
% 3.64/0.97      inference(cnf_transformation,[],[f79]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_466,plain,
% 3.64/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.64/0.97      | sK2 != k1_xboole_0
% 3.64/0.97      | sK1 != X1
% 3.64/0.97      | sK4 != X0
% 3.64/0.97      | k1_xboole_0 = X1
% 3.64/0.97      | k1_xboole_0 = X0 ),
% 3.64/0.97      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_467,plain,
% 3.64/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 3.64/0.97      | sK2 != k1_xboole_0
% 3.64/0.97      | k1_xboole_0 = sK1
% 3.64/0.97      | k1_xboole_0 = sK4 ),
% 3.64/0.97      inference(unflattening,[status(thm)],[c_466]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1279,plain,
% 3.64/0.97      ( sK2 != k1_xboole_0
% 3.64/0.97      | k1_xboole_0 = sK1
% 3.64/0.97      | k1_xboole_0 = sK4
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1296,plain,
% 3.64/0.97      ( sK2 != k1_xboole_0
% 3.64/0.97      | sK1 = k1_xboole_0
% 3.64/0.97      | sK4 = k1_xboole_0
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.64/0.97      inference(demodulation,[status(thm)],[c_1279,c_4]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_6,plain,
% 3.64/0.97      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.64/0.97      | k1_xboole_0 = X1
% 3.64/0.97      | k1_xboole_0 = X0 ),
% 3.64/0.97      inference(cnf_transformation,[],[f43]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_94,plain,
% 3.64/0.97      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.64/0.97      | k1_xboole_0 = k1_xboole_0 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_5,plain,
% 3.64/0.97      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.64/0.97      inference(cnf_transformation,[],[f76]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_95,plain,
% 3.64/0.97      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_5]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_783,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1330,plain,
% 3.64/0.97      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_783]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1385,plain,
% 3.64/0.97      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_1330]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1553,plain,
% 3.64/0.97      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_783]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1554,plain,
% 3.64/0.97      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_1553]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1857,plain,
% 3.64/0.97      ( sK2 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.64/0.97      inference(global_propositional_subsumption,
% 3.64/0.97                [status(thm)],
% 3.64/0.97                [c_1296,c_29,c_94,c_95,c_1385,c_1452,c_1554]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13348,plain,
% 3.64/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.64/0.97      | sK1 = k1_xboole_0
% 3.64/0.97      | sK4 != k1_xboole_0 ),
% 3.64/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_13341]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13366,plain,
% 3.64/0.97      ( sK4 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.64/0.97      inference(global_propositional_subsumption,
% 3.64/0.97                [status(thm)],
% 3.64/0.97                [c_13341,c_1336,c_1452,c_1857,c_1891,c_2996,c_3140,c_3618,
% 3.64/0.97                 c_5208,c_13348]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13367,plain,
% 3.64/0.97      ( sK1 = k1_xboole_0 | sK4 != k1_xboole_0 ),
% 3.64/0.97      inference(renaming,[status(thm)],[c_13366]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13340,plain,
% 3.64/0.97      ( sK1 = k1_xboole_0
% 3.64/0.97      | r1_tarski(k2_relat_1(sK4),k1_xboole_0) = iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_13319,c_2995]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3320,plain,
% 3.64/0.97      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 3.64/0.97      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.64/0.97      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.64/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_1286,c_1291]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1,plain,
% 3.64/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.64/0.97      inference(cnf_transformation,[],[f42]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1294,plain,
% 3.64/0.97      ( X0 = X1
% 3.64/0.97      | r1_tarski(X0,X1) != iProver_top
% 3.64/0.97      | r1_tarski(X1,X0) != iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_6445,plain,
% 3.64/0.97      ( k2_zfmisc_1(X0,X1) = X2
% 3.64/0.97      | r1_tarski(k2_zfmisc_1(X0,X1),X2) != iProver_top
% 3.64/0.97      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.64/0.97      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.64/0.97      | v1_relat_1(X2) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_3320,c_1294]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_9139,plain,
% 3.64/0.97      ( k2_zfmisc_1(X0,k1_xboole_0) = X1
% 3.64/0.97      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 3.64/0.97      | r1_tarski(k2_relat_1(X1),k1_xboole_0) != iProver_top
% 3.64/0.97      | r1_tarski(k1_xboole_0,X1) != iProver_top
% 3.64/0.97      | v1_relat_1(X1) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_4,c_6445]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_9142,plain,
% 3.64/0.97      ( k1_xboole_0 = X0
% 3.64/0.97      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.64/0.97      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.64/0.97      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 3.64/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.97      inference(demodulation,[status(thm)],[c_9139,c_4]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_0,plain,
% 3.64/0.97      ( v1_xboole_0(k1_xboole_0) ),
% 3.64/0.97      inference(cnf_transformation,[],[f39]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_9,plain,
% 3.64/0.97      ( ~ r2_hidden(X0,X1)
% 3.64/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.64/0.97      | ~ v1_xboole_0(X2) ),
% 3.64/0.97      inference(cnf_transformation,[],[f48]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_383,plain,
% 3.64/0.97      ( ~ r2_hidden(X0,X1)
% 3.64/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.64/0.97      | k1_xboole_0 != X2 ),
% 3.64/0.97      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_384,plain,
% 3.64/0.97      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
% 3.64/0.97      inference(unflattening,[status(thm)],[c_383]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_21,plain,
% 3.64/0.97      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.64/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_398,plain,
% 3.64/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 3.64/0.97      | X1 != X0
% 3.64/0.97      | sK0(X1) != X2
% 3.64/0.97      | k1_xboole_0 = X1 ),
% 3.64/0.97      inference(resolution_lifted,[status(thm)],[c_384,c_21]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_399,plain,
% 3.64/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 ),
% 3.64/0.97      inference(unflattening,[status(thm)],[c_398]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_400,plain,
% 3.64/0.97      ( k1_xboole_0 = X0
% 3.64/0.97      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3318,plain,
% 3.64/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.64/0.97      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.64/0.97      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.64/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_4,c_1286]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3895,plain,
% 3.64/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.64/0.97      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.64/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_1293,c_3318]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_9241,plain,
% 3.64/0.97      ( r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.64/0.97      | k1_xboole_0 = X0
% 3.64/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.97      inference(global_propositional_subsumption,
% 3.64/0.97                [status(thm)],
% 3.64/0.97                [c_9142,c_400,c_3895]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_9242,plain,
% 3.64/0.97      ( k1_xboole_0 = X0
% 3.64/0.97      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.64/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.97      inference(renaming,[status(thm)],[c_9241]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13410,plain,
% 3.64/0.97      ( sK1 = k1_xboole_0
% 3.64/0.97      | sK4 = k1_xboole_0
% 3.64/0.97      | v1_relat_1(sK4) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_13340,c_9242]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13475,plain,
% 3.64/0.97      ( sK1 = k1_xboole_0 ),
% 3.64/0.97      inference(global_propositional_subsumption,
% 3.64/0.97                [status(thm)],
% 3.64/0.97                [c_13334,c_3139,c_13367,c_13410]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_24,plain,
% 3.64/0.97      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.64/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.64/0.97      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.64/0.97      inference(cnf_transformation,[],[f80]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_486,plain,
% 3.64/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.64/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.64/0.97      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.64/0.97      | sK3 != X1
% 3.64/0.97      | sK1 != k1_xboole_0
% 3.64/0.97      | sK4 != X0 ),
% 3.64/0.97      inference(resolution_lifted,[status(thm)],[c_24,c_166]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_487,plain,
% 3.64/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.64/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 3.64/0.97      | k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.64/0.97      | sK1 != k1_xboole_0 ),
% 3.64/0.97      inference(unflattening,[status(thm)],[c_486]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1278,plain,
% 3.64/0.97      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.64/0.97      | sK1 != k1_xboole_0
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1297,plain,
% 3.64/0.97      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.64/0.97      | sK1 != k1_xboole_0
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.64/0.97      inference(demodulation,[status(thm)],[c_1278,c_5]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13523,plain,
% 3.64/0.97      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.64/0.97      | k1_xboole_0 != k1_xboole_0
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.64/0.97      inference(demodulation,[status(thm)],[c_13475,c_1297]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13534,plain,
% 3.64/0.97      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.64/0.97      inference(equality_resolution_simp,[status(thm)],[c_13523]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13535,plain,
% 3.64/0.97      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.64/0.97      inference(demodulation,[status(thm)],[c_13534,c_5]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1353,plain,
% 3.64/0.97      ( ~ r1_tarski(X0,X1)
% 3.64/0.97      | r1_tarski(sK1,k1_xboole_0)
% 3.64/0.97      | sK1 != X0
% 3.64/0.97      | k1_xboole_0 != X1 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_784]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1354,plain,
% 3.64/0.97      ( sK1 != X0
% 3.64/0.97      | k1_xboole_0 != X1
% 3.64/0.97      | r1_tarski(X0,X1) != iProver_top
% 3.64/0.97      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_1353]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1356,plain,
% 3.64/0.97      ( sK1 != k1_xboole_0
% 3.64/0.97      | k1_xboole_0 != k1_xboole_0
% 3.64/0.97      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 3.64/0.97      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_1354]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3319,plain,
% 3.64/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.64/0.97      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 3.64/0.97      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.64/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_5,c_1286]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3904,plain,
% 3.64/0.97      ( sK2 = k1_xboole_0
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.64/0.97      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 3.64/0.97      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 3.64/0.97      | v1_relat_1(sK4) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_3618,c_3319]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_36,plain,
% 3.64/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1406,plain,
% 3.64/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
% 3.64/0.97      | ~ r1_tarski(sK1,k1_xboole_0) ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1407,plain,
% 3.64/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.64/0.97      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_1406]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1455,plain,
% 3.64/0.97      ( sK4 = sK4 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_782]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1536,plain,
% 3.64/0.97      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_399]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1537,plain,
% 3.64/0.97      ( k1_xboole_0 = sK1
% 3.64/0.97      | m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_1536]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1694,plain,
% 3.64/0.97      ( X0 != X1 | X0 = k2_zfmisc_1(X2,X3) | k2_zfmisc_1(X2,X3) != X1 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_783]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1695,plain,
% 3.64/0.97      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.64/0.97      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.64/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_1694]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1838,plain,
% 3.64/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~ r1_tarski(sK4,X0) ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1839,plain,
% 3.64/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) = iProver_top
% 3.64/0.97      | r1_tarski(sK4,X0) != iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_1838]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1841,plain,
% 3.64/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.64/0.97      | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_1839]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1589,plain,
% 3.64/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | r1_tarski(sK4,X0) ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_8]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1919,plain,
% 3.64/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.64/0.97      | r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_1589]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1920,plain,
% 3.64/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.64/0.97      | r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_1919]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1597,plain,
% 3.64/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,X2) | X2 != X1 | sK4 != X0 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_784]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_2022,plain,
% 3.64/0.97      ( ~ r1_tarski(sK4,X0) | r1_tarski(sK4,X1) | X1 != X0 | sK4 != sK4 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_1597]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3332,plain,
% 3.64/0.97      ( r1_tarski(sK4,X0)
% 3.64/0.97      | ~ r1_tarski(sK4,k2_zfmisc_1(X1,X2))
% 3.64/0.97      | X0 != k2_zfmisc_1(X1,X2)
% 3.64/0.97      | sK4 != sK4 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_2022]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3348,plain,
% 3.64/0.97      ( X0 != k2_zfmisc_1(X1,X2)
% 3.64/0.97      | sK4 != sK4
% 3.64/0.97      | r1_tarski(sK4,X0) = iProver_top
% 3.64/0.97      | r1_tarski(sK4,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_3332]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3350,plain,
% 3.64/0.97      ( sK4 != sK4
% 3.64/0.97      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.64/0.97      | r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.64/0.97      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_3348]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_2779,plain,
% 3.64/0.97      ( r1_tarski(sK4,X0)
% 3.64/0.97      | ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))
% 3.64/0.97      | X0 != k2_zfmisc_1(sK1,sK2)
% 3.64/0.97      | sK4 != sK4 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_2022]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3531,plain,
% 3.64/0.97      ( r1_tarski(sK4,k2_zfmisc_1(X0,X1))
% 3.64/0.97      | ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))
% 3.64/0.97      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2)
% 3.64/0.97      | sK4 != sK4 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_2779]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3532,plain,
% 3.64/0.97      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2)
% 3.64/0.97      | sK4 != sK4
% 3.64/0.97      | r1_tarski(sK4,k2_zfmisc_1(X0,X1)) = iProver_top
% 3.64/0.97      | r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) != iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_3531]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3534,plain,
% 3.64/0.97      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK1,sK2)
% 3.64/0.97      | sK4 != sK4
% 3.64/0.97      | r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.64/0.97      | r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_3532]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_785,plain,
% 3.64/0.97      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 3.64/0.97      theory(equality) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_4486,plain,
% 3.64/0.97      ( X0 != sK2 | X1 != sK1 | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK1,sK2) ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_785]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_4487,plain,
% 3.64/0.97      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK1,sK2)
% 3.64/0.97      | k1_xboole_0 != sK2
% 3.64/0.97      | k1_xboole_0 != sK1 ),
% 3.64/0.97      inference(instantiation,[status(thm)],[c_4486]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_4515,plain,
% 3.64/0.97      ( r1_tarski(sK1,k1_xboole_0) != iProver_top
% 3.64/0.97      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 3.64/0.97      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.64/0.97      inference(global_propositional_subsumption,
% 3.64/0.97                [status(thm)],
% 3.64/0.97                [c_3904,c_36,c_94,c_95,c_1407,c_1455,c_1537,c_1554,c_1695,
% 3.64/0.97                 c_1841,c_1920,c_3139,c_3350,c_3534,c_4487]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_4516,plain,
% 3.64/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.64/0.97      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 3.64/0.97      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 3.64/0.97      inference(renaming,[status(thm)],[c_4515]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_4521,plain,
% 3.64/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.64/0.97      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_1293,c_4516]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_14157,plain,
% 3.64/0.97      ( k1_relset_1(k1_xboole_0,sK3,sK4) != k1_xboole_0 ),
% 3.64/0.97      inference(global_propositional_subsumption,
% 3.64/0.97                [status(thm)],
% 3.64/0.97                [c_13535,c_94,c_95,c_98,c_1356,c_3139,c_4521,c_13367,c_13410]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13521,plain,
% 3.64/0.97      ( r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,sK2)) = iProver_top ),
% 3.64/0.97      inference(demodulation,[status(thm)],[c_13475,c_2401]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13536,plain,
% 3.64/0.97      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.64/0.97      inference(demodulation,[status(thm)],[c_13521,c_5]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1292,plain,
% 3.64/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.64/0.97      | r1_tarski(X0,X1) != iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1281,plain,
% 3.64/0.97      ( k1_xboole_0 = X0
% 3.64/0.97      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_2847,plain,
% 3.64/0.97      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_1292,c_1281]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13754,plain,
% 3.64/0.97      ( sK4 = k1_xboole_0 ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_13536,c_2847]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_14159,plain,
% 3.64/0.97      ( k1_relset_1(k1_xboole_0,sK3,k1_xboole_0) != k1_xboole_0 ),
% 3.64/0.97      inference(light_normalisation,[status(thm)],[c_14157,c_13754]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_18,plain,
% 3.64/0.97      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.64/0.97      inference(cnf_transformation,[],[f57]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1285,plain,
% 3.64/0.97      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_2050,plain,
% 3.64/0.97      ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_4,c_1285]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_2591,plain,
% 3.64/0.97      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_2050,c_1281]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_13,plain,
% 3.64/0.97      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.64/0.97      inference(cnf_transformation,[],[f53]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_2598,plain,
% 3.64/0.97      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_2591,c_13]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_12,plain,
% 3.64/0.97      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
% 3.64/0.97      inference(cnf_transformation,[],[f51]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1289,plain,
% 3.64/0.97      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
% 3.64/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_1983,plain,
% 3.64/0.97      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_5,c_1289]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_2649,plain,
% 3.64/0.97      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.64/0.97      inference(demodulation,[status(thm)],[c_2598,c_1983]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_3458,plain,
% 3.64/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.64/0.97      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_1292,c_1288]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_7260,plain,
% 3.64/0.97      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_2649,c_3458]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_14,plain,
% 3.64/0.97      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.64/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_2597,plain,
% 3.64/0.97      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.64/0.97      inference(superposition,[status(thm)],[c_2591,c_14]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_7263,plain,
% 3.64/0.97      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 3.64/0.97      inference(light_normalisation,[status(thm)],[c_7260,c_2597]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_14160,plain,
% 3.64/0.97      ( k1_xboole_0 != k1_xboole_0 ),
% 3.64/0.97      inference(demodulation,[status(thm)],[c_14159,c_7263]) ).
% 3.64/0.97  
% 3.64/0.97  cnf(c_14161,plain,
% 3.64/0.97      ( $false ),
% 3.64/0.97      inference(equality_resolution_simp,[status(thm)],[c_14160]) ).
% 3.64/0.97  
% 3.64/0.97  
% 3.64/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.64/0.97  
% 3.64/0.97  ------                               Statistics
% 3.64/0.97  
% 3.64/0.97  ------ General
% 3.64/0.97  
% 3.64/0.97  abstr_ref_over_cycles:                  0
% 3.64/0.97  abstr_ref_under_cycles:                 0
% 3.64/0.97  gc_basic_clause_elim:                   0
% 3.64/0.97  forced_gc_time:                         0
% 3.64/0.97  parsing_time:                           0.008
% 3.64/0.97  unif_index_cands_time:                  0.
% 3.64/0.97  unif_index_add_time:                    0.
% 3.64/0.97  orderings_time:                         0.
% 3.64/0.97  out_proof_time:                         0.016
% 3.64/0.97  total_time:                             0.454
% 3.64/0.97  num_of_symbols:                         52
% 3.64/0.97  num_of_terms:                           10483
% 3.64/0.97  
% 3.64/0.97  ------ Preprocessing
% 3.64/0.97  
% 3.64/0.97  num_of_splits:                          0
% 3.64/0.97  num_of_split_atoms:                     0
% 3.64/0.97  num_of_reused_defs:                     0
% 3.64/0.97  num_eq_ax_congr_red:                    14
% 3.64/0.97  num_of_sem_filtered_clauses:            2
% 3.64/0.97  num_of_subtypes:                        0
% 3.64/0.97  monotx_restored_types:                  0
% 3.64/0.97  sat_num_of_epr_types:                   0
% 3.64/0.97  sat_num_of_non_cyclic_types:            0
% 3.64/0.97  sat_guarded_non_collapsed_types:        0
% 3.64/0.97  num_pure_diseq_elim:                    0
% 3.64/0.97  simp_replaced_by:                       0
% 3.64/0.97  res_preprocessed:                       145
% 3.64/0.97  prep_upred:                             0
% 3.64/0.97  prep_unflattend:                        40
% 3.64/0.97  smt_new_axioms:                         0
% 3.64/0.97  pred_elim_cands:                        3
% 3.64/0.97  pred_elim:                              3
% 3.64/0.97  pred_elim_cl:                           3
% 3.64/0.97  pred_elim_cycles:                       5
% 3.64/0.97  merged_defs:                            8
% 3.64/0.97  merged_defs_ncl:                        0
% 3.64/0.97  bin_hyper_res:                          9
% 3.64/0.97  prep_cycles:                            4
% 3.64/0.97  pred_elim_time:                         0.007
% 3.64/0.97  splitting_time:                         0.
% 3.64/0.97  sem_filter_time:                        0.
% 3.64/0.97  monotx_time:                            0.
% 3.64/0.97  subtype_inf_time:                       0.
% 3.64/0.97  
% 3.64/0.97  ------ Problem properties
% 3.64/0.97  
% 3.64/0.97  clauses:                                29
% 3.64/0.97  conjectures:                            3
% 3.64/0.97  epr:                                    4
% 3.64/0.97  horn:                                   26
% 3.64/0.97  ground:                                 10
% 3.64/0.97  unary:                                  10
% 3.64/0.97  binary:                                 10
% 3.64/0.97  lits:                                   62
% 3.64/0.97  lits_eq:                                32
% 3.64/0.97  fd_pure:                                0
% 3.64/0.97  fd_pseudo:                              0
% 3.64/0.97  fd_cond:                                4
% 3.64/0.97  fd_pseudo_cond:                         1
% 3.64/0.97  ac_symbols:                             0
% 3.64/0.97  
% 3.64/0.97  ------ Propositional Solver
% 3.64/0.97  
% 3.64/0.97  prop_solver_calls:                      31
% 3.64/0.97  prop_fast_solver_calls:                 1384
% 3.64/0.97  smt_solver_calls:                       0
% 3.64/0.97  smt_fast_solver_calls:                  0
% 3.64/0.97  prop_num_of_clauses:                    5775
% 3.64/0.97  prop_preprocess_simplified:             13214
% 3.64/0.97  prop_fo_subsumed:                       54
% 3.64/0.97  prop_solver_time:                       0.
% 3.64/0.97  smt_solver_time:                        0.
% 3.64/0.97  smt_fast_solver_time:                   0.
% 3.64/0.97  prop_fast_solver_time:                  0.
% 3.64/0.97  prop_unsat_core_time:                   0.
% 3.64/0.97  
% 3.64/0.97  ------ QBF
% 3.64/0.97  
% 3.64/0.97  qbf_q_res:                              0
% 3.64/0.97  qbf_num_tautologies:                    0
% 3.64/0.97  qbf_prep_cycles:                        0
% 3.64/0.97  
% 3.64/0.97  ------ BMC1
% 3.64/0.97  
% 3.64/0.97  bmc1_current_bound:                     -1
% 3.64/0.97  bmc1_last_solved_bound:                 -1
% 3.64/0.97  bmc1_unsat_core_size:                   -1
% 3.64/0.97  bmc1_unsat_core_parents_size:           -1
% 3.64/0.97  bmc1_merge_next_fun:                    0
% 3.64/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.64/0.97  
% 3.64/0.97  ------ Instantiation
% 3.64/0.97  
% 3.64/0.97  inst_num_of_clauses:                    1835
% 3.64/0.97  inst_num_in_passive:                    981
% 3.64/0.97  inst_num_in_active:                     750
% 3.64/0.97  inst_num_in_unprocessed:                104
% 3.64/0.97  inst_num_of_loops:                      1090
% 3.64/0.97  inst_num_of_learning_restarts:          0
% 3.64/0.97  inst_num_moves_active_passive:          336
% 3.64/0.97  inst_lit_activity:                      0
% 3.64/0.97  inst_lit_activity_moves:                0
% 3.64/0.97  inst_num_tautologies:                   0
% 3.64/0.97  inst_num_prop_implied:                  0
% 3.64/0.97  inst_num_existing_simplified:           0
% 3.64/0.97  inst_num_eq_res_simplified:             0
% 3.64/0.97  inst_num_child_elim:                    0
% 3.64/0.97  inst_num_of_dismatching_blockings:      525
% 3.64/0.97  inst_num_of_non_proper_insts:           2590
% 3.64/0.97  inst_num_of_duplicates:                 0
% 3.64/0.97  inst_inst_num_from_inst_to_res:         0
% 3.64/0.97  inst_dismatching_checking_time:         0.
% 3.64/0.97  
% 3.64/0.97  ------ Resolution
% 3.64/0.97  
% 3.64/0.97  res_num_of_clauses:                     0
% 3.64/0.97  res_num_in_passive:                     0
% 3.64/0.97  res_num_in_active:                      0
% 3.64/0.97  res_num_of_loops:                       149
% 3.64/0.97  res_forward_subset_subsumed:            162
% 3.64/0.97  res_backward_subset_subsumed:           0
% 3.64/0.97  res_forward_subsumed:                   0
% 3.64/0.97  res_backward_subsumed:                  0
% 3.64/0.97  res_forward_subsumption_resolution:     0
% 3.64/0.97  res_backward_subsumption_resolution:    0
% 3.64/0.97  res_clause_to_clause_subsumption:       2192
% 3.64/0.97  res_orphan_elimination:                 0
% 3.64/0.97  res_tautology_del:                      176
% 3.64/0.97  res_num_eq_res_simplified:              1
% 3.64/0.97  res_num_sel_changes:                    0
% 3.64/0.97  res_moves_from_active_to_pass:          0
% 3.64/0.97  
% 3.64/0.97  ------ Superposition
% 3.64/0.97  
% 3.64/0.97  sup_time_total:                         0.
% 3.64/0.97  sup_time_generating:                    0.
% 3.64/0.97  sup_time_sim_full:                      0.
% 3.64/0.97  sup_time_sim_immed:                     0.
% 3.64/0.97  
% 3.64/0.97  sup_num_of_clauses:                     236
% 3.64/0.97  sup_num_in_active:                      115
% 3.64/0.97  sup_num_in_passive:                     121
% 3.64/0.97  sup_num_of_loops:                       217
% 3.64/0.97  sup_fw_superposition:                   422
% 3.64/0.97  sup_bw_superposition:                   164
% 3.64/0.97  sup_immediate_simplified:               267
% 3.64/0.97  sup_given_eliminated:                   6
% 3.64/0.97  comparisons_done:                       0
% 3.64/0.97  comparisons_avoided:                    81
% 3.64/0.97  
% 3.64/0.97  ------ Simplifications
% 3.64/0.97  
% 3.64/0.97  
% 3.64/0.97  sim_fw_subset_subsumed:                 36
% 3.64/0.97  sim_bw_subset_subsumed:                 37
% 3.64/0.97  sim_fw_subsumed:                        25
% 3.64/0.97  sim_bw_subsumed:                        46
% 3.64/0.97  sim_fw_subsumption_res:                 0
% 3.64/0.97  sim_bw_subsumption_res:                 0
% 3.64/0.97  sim_tautology_del:                      16
% 3.64/0.97  sim_eq_tautology_del:                   87
% 3.64/0.97  sim_eq_res_simp:                        2
% 3.64/0.97  sim_fw_demodulated:                     100
% 3.64/0.97  sim_bw_demodulated:                     79
% 3.64/0.97  sim_light_normalised:                   153
% 3.64/0.97  sim_joinable_taut:                      0
% 3.64/0.97  sim_joinable_simp:                      0
% 3.64/0.97  sim_ac_normalised:                      0
% 3.64/0.97  sim_smt_subsumption:                    0
% 3.64/0.97  
%------------------------------------------------------------------------------
