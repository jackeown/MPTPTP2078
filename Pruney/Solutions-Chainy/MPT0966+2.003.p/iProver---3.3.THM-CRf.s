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
% DateTime   : Thu Dec  3 12:00:31 EST 2020

% Result     : Theorem 15.19s
% Output     : CNFRefutation 15.19s
% Verified   : 
% Statistics : Number of formulae       :  303 (43668 expanded)
%              Number of clauses        :  231 (17038 expanded)
%              Number of leaves         :   21 (7962 expanded)
%              Depth                    :   40
%              Number of atoms          :  855 (206206 expanded)
%              Number of equality atoms :  522 (70043 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f59,plain,(
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
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
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
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

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
    inference(ennf_transformation,[],[f15])).

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
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
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
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f37])).

fof(f66,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f43])).

fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f44])).

fof(f69,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f62])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1251,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_30])).

cnf(c_514,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_516,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_29])).

cnf(c_1245,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1249,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3590,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1245,c_1249])).

cnf(c_3975,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_516,c_3590])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_10])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_382,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_378,c_14])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_382])).

cnf(c_1243,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_2063,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1245,c_1243])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1248,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2667,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1245,c_1248])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1246,plain,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2750,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2667,c_1246])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1247,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3589,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1247,c_1249])).

cnf(c_17239,plain,
    ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2750,c_3589])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1327,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1392,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1327])).

cnf(c_1393,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1392])).

cnf(c_17817,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17239,c_34,c_1393])).

cnf(c_17818,plain,
    ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_17817])).

cnf(c_17826,plain,
    ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2063,c_17818])).

cnf(c_23,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_165,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_31])).

cnf(c_166,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(renaming,[status(thm)],[c_165])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_166])).

cnf(c_501,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_1237,plain,
    ( k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_17922,plain,
    ( k1_relat_1(sK3) != sK0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17826,c_1237])).

cnf(c_1297,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1298,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1297])).

cnf(c_17925,plain,
    ( sK2 = k1_xboole_0
    | k1_relat_1(sK3) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17922,c_34,c_1298,c_1393,c_2063,c_2750])).

cnf(c_17926,plain,
    ( k1_relat_1(sK3) != sK0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_17925])).

cnf(c_17927,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3975,c_17926])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_95,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_96,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_98,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_763,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1314,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_1316,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_452,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_1240,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1257,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1240,c_3])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_762,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1291,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_1352,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1291])).

cnf(c_761,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1482,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_1817,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_1818,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(c_1866,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1257,c_27,c_95,c_96,c_1352,c_1482,c_1818])).

cnf(c_1885,plain,
    ( X0 != X1
    | X0 = sK0
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_4507,plain,
    ( k1_relat_1(sK3) != X0
    | k1_relat_1(sK3) = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1885])).

cnf(c_4515,plain,
    ( k1_relat_1(sK3) = sK0
    | k1_relat_1(sK3) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4507])).

cnf(c_3365,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1247])).

cnf(c_4498,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2750,c_3365])).

cnf(c_4978,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4498,c_34,c_1393])).

cnf(c_4979,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4978])).

cnf(c_4983,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3975,c_4979])).

cnf(c_1485,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_12])).

cnf(c_403,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_399,c_14])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_403])).

cnf(c_1616,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r1_tarski(k2_relat_1(sK3),X1) ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_1617,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1616])).

cnf(c_1619,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1617])).

cnf(c_766,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1448,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | X2 != X0
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != X1 ),
    inference(instantiation,[status(thm)],[c_766])).

cnf(c_1687,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | X0 != sK3
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1448])).

cnf(c_1730,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1687])).

cnf(c_1731,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1730])).

cnf(c_1733,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1731])).

cnf(c_765,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1781,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_1782,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK0,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1781])).

cnf(c_764,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_2356,plain,
    ( X0 != sK1
    | X1 != sK0
    | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_2357,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != sK1
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2356])).

cnf(c_3364,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1247])).

cnf(c_4407,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2063,c_3364])).

cnf(c_5050,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4983,c_34,c_27,c_95,c_96,c_1393,c_1485,c_1619,c_1733,c_1782,c_1818,c_2357,c_4407])).

cnf(c_5052,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5050])).

cnf(c_1242,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_1640,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1245,c_1242])).

cnf(c_17241,plain,
    ( k1_relset_1(X0,sK1,sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1640,c_3589])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1847,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1848,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1847])).

cnf(c_1850,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1848])).

cnf(c_1981,plain,
    ( r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3888,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_3889,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3888])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1253,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2064,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1243])).

cnf(c_2569,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1253,c_2064])).

cnf(c_3977,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK0,X0) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3975,c_2569])).

cnf(c_3981,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3977])).

cnf(c_5055,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5050,c_2064])).

cnf(c_5063,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5055])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2022,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK3))
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | k2_relat_1(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6128,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | k2_relat_1(sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2022])).

cnf(c_1621,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK3),X2)
    | X2 != X1
    | k2_relat_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_2027,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),X0)
    | r1_tarski(k2_relat_1(sK3),X1)
    | X1 != X0
    | k2_relat_1(sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1621])).

cnf(c_10824,plain,
    ( r1_tarski(k2_relat_1(sK3),X0)
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | X0 != sK2
    | k2_relat_1(sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2027])).

cnf(c_10825,plain,
    ( X0 != sK2
    | k2_relat_1(sK3) != k2_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10824])).

cnf(c_10827,plain,
    ( k2_relat_1(sK3) != k2_relat_1(sK3)
    | k1_xboole_0 != sK2
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10825])).

cnf(c_17267,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k1_relset_1(X0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17241])).

cnf(c_17976,plain,
    ( k1_relset_1(X0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17241,c_29,c_34,c_95,c_96,c_98,c_1316,c_1392,c_1393,c_1850,c_1866,c_1981,c_2750,c_3889,c_3981,c_4407,c_5055,c_5063,c_6128,c_10827,c_17267,c_17927])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_487,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK1 != X1
    | sK0 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_488,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_1238,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_1256,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1238,c_4])).

cnf(c_17979,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17976,c_1256])).

cnf(c_17980,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_relat_1(sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17979])).

cnf(c_17983,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17927,c_34,c_95,c_96,c_98,c_1298,c_1316,c_1393,c_1866,c_2063,c_2750,c_4515,c_5052,c_17922,c_17980])).

cnf(c_17997,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17983,c_2750])).

cnf(c_4820,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4407,c_34,c_1393])).

cnf(c_4821,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4820])).

cnf(c_18054,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_17997,c_4821])).

cnf(c_18721,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_18054,c_2064])).

cnf(c_1254,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2062,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1253,c_1243])).

cnf(c_6000,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_2062])).

cnf(c_6439,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_6000])).

cnf(c_1255,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6724,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6439,c_1255])).

cnf(c_19041,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_18721,c_6724])).

cnf(c_21172,plain,
    ( k1_relat_1(k1_xboole_0) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19041,c_3975])).

cnf(c_524,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | sK1 != sK2
    | sK0 != sK0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_166,c_30])).

cnf(c_525,plain,
    ( sK1 != sK2
    | sK0 != sK0
    | sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_1308,plain,
    ( sK1 != X0
    | sK1 = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_1309,plain,
    ( sK1 = sK2
    | sK1 != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1308])).

cnf(c_21252,plain,
    ( k1_relat_1(k1_xboole_0) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21172,c_34,c_95,c_96,c_98,c_525,c_1298,c_1309,c_1316,c_1393,c_1482,c_1485,c_1866,c_2063,c_2750,c_4515,c_5052,c_17922,c_17927,c_17980])).

cnf(c_21272,plain,
    ( r1_tarski(sK0,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_21252,c_6439])).

cnf(c_2057,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1253,c_1242])).

cnf(c_5164,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_2057])).

cnf(c_5305,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5164,c_1255])).

cnf(c_21672,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_21272,c_5305])).

cnf(c_1252,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3366,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1247,c_1252])).

cnf(c_8882,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_3366])).

cnf(c_4405,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_3364])).

cnf(c_8894,plain,
    ( r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8882,c_2064,c_4405])).

cnf(c_8895,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8894])).

cnf(c_22490,plain,
    ( r1_tarski(k2_zfmisc_1(X0,sK0),k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21672,c_8895])).

cnf(c_64020,plain,
    ( r1_tarski(k2_zfmisc_1(X0,sK0),k1_xboole_0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22490,c_34,c_95,c_96,c_98,c_525,c_1298,c_1309,c_1316,c_1393,c_1482,c_1485,c_1850,c_1866,c_1981,c_2063,c_2750,c_3889,c_3981,c_4407,c_4515,c_5052,c_6128,c_10827,c_17922,c_17927,c_17980])).

cnf(c_8884,plain,
    ( k2_zfmisc_1(X0,X1) = X2
    | r1_tarski(k2_zfmisc_1(X0,X1),X2) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3366,c_1255])).

cnf(c_64106,plain,
    ( k2_zfmisc_1(X0,sK0) = k1_xboole_0
    | r1_tarski(k2_relat_1(k1_xboole_0),sK0) != iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),X0) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_64020,c_8884])).

cnf(c_5304,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_5164])).

cnf(c_5333,plain,
    ( k2_relat_1(k1_xboole_0) = X0
    | r1_tarski(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5304,c_1255])).

cnf(c_9797,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6439,c_5333])).

cnf(c_21266,plain,
    ( k2_relat_1(k1_xboole_0) = sK0 ),
    inference(demodulation,[status(thm)],[c_21252,c_9797])).

cnf(c_64107,plain,
    ( k2_zfmisc_1(X0,sK0) = k1_xboole_0
    | r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(sK0,sK0) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_64106,c_21252,c_21266])).

cnf(c_73,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_75,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_97,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_99,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_229,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_230,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_229])).

cnf(c_285,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_230])).

cnf(c_1651,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_1652,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1651])).

cnf(c_1654,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_1676,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | X2 != X0
    | k2_zfmisc_1(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_1677,plain,
    ( X0 != X1
    | k2_zfmisc_1(X2,X3) != X4
    | r1_tarski(X1,X4) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X2,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1676])).

cnf(c_1679,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1677])).

cnf(c_8621,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_8622,plain,
    ( r1_tarski(sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8621])).

cnf(c_64334,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top
    | k2_zfmisc_1(X0,sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_64107,c_34,c_75,c_95,c_96,c_98,c_99,c_525,c_1298,c_1309,c_1316,c_1393,c_1482,c_1485,c_1654,c_1679,c_1850,c_1866,c_1981,c_2063,c_2750,c_3889,c_3977,c_4407,c_4515,c_5052,c_6128,c_8622,c_10827,c_17922,c_17927,c_17980])).

cnf(c_64335,plain,
    ( k2_zfmisc_1(X0,sK0) = k1_xboole_0
    | v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_64334])).

cnf(c_64338,plain,
    ( k2_zfmisc_1(X0,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1251,c_64335])).

cnf(c_64389,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_64338,c_5])).

cnf(c_1810,plain,
    ( k2_zfmisc_1(X0,sK0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_22,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_471,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != X1
    | sK0 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_166])).

cnf(c_472,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_1239,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_472])).

cnf(c_1258,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1239,c_4])).

cnf(c_17999,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17983,c_1258])).

cnf(c_18002,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17999,c_3])).

cnf(c_1849,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_2751,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2750])).

cnf(c_4822,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4821])).

cnf(c_4259,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != X0
    | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_7847,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_relat_1(sK3)
    | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4259])).

cnf(c_10826,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | k2_relat_1(sK3) != k2_relat_1(sK3)
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_10824])).

cnf(c_15349,plain,
    ( k1_relat_1(sK3) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_15350,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15349])).

cnf(c_17824,plain,
    ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2569,c_17818])).

cnf(c_17829,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17824])).

cnf(c_17831,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_17829])).

cnf(c_18330,plain,
    ( sK0 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18002,c_34,c_95,c_96,c_98,c_1258,c_1298,c_1316,c_1393,c_1849,c_1866,c_1981,c_2063,c_2750,c_2751,c_3889,c_4407,c_4515,c_4822,c_5052,c_6128,c_7847,c_10826,c_10827,c_15350,c_17831,c_17922,c_17927,c_17979,c_17980])).

cnf(c_65006,plain,
    ( k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_64389,c_34,c_95,c_96,c_98,c_1258,c_1298,c_1316,c_1352,c_1393,c_1482,c_1810,c_1849,c_1866,c_1981,c_2063,c_2750,c_2751,c_3889,c_4407,c_4515,c_4822,c_5052,c_6128,c_7847,c_10826,c_10827,c_15350,c_17831,c_17922,c_17927,c_17979,c_17980,c_64338])).

cnf(c_590,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | sK1 != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_524])).

cnf(c_1236,plain,
    ( sK1 != sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_18000,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17983,c_1236])).

cnf(c_18001,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18000,c_3])).

cnf(c_18296,plain,
    ( sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18001,c_34,c_95,c_96,c_98,c_525,c_1298,c_1309,c_1316,c_1393,c_1482,c_1485,c_1866,c_2063,c_2750,c_4515,c_5052,c_17922,c_17927,c_17980])).

cnf(c_65259,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_65006,c_18296])).

cnf(c_65276,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_65259])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.19/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.19/2.49  
% 15.19/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.19/2.49  
% 15.19/2.49  ------  iProver source info
% 15.19/2.49  
% 15.19/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.19/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.19/2.49  git: non_committed_changes: false
% 15.19/2.49  git: last_make_outside_of_git: false
% 15.19/2.49  
% 15.19/2.49  ------ 
% 15.19/2.49  
% 15.19/2.49  ------ Input Options
% 15.19/2.49  
% 15.19/2.49  --out_options                           all
% 15.19/2.49  --tptp_safe_out                         true
% 15.19/2.49  --problem_path                          ""
% 15.19/2.49  --include_path                          ""
% 15.19/2.49  --clausifier                            res/vclausify_rel
% 15.19/2.49  --clausifier_options                    ""
% 15.19/2.49  --stdin                                 false
% 15.19/2.49  --stats_out                             all
% 15.19/2.49  
% 15.19/2.49  ------ General Options
% 15.19/2.49  
% 15.19/2.49  --fof                                   false
% 15.19/2.49  --time_out_real                         305.
% 15.19/2.49  --time_out_virtual                      -1.
% 15.19/2.49  --symbol_type_check                     false
% 15.19/2.49  --clausify_out                          false
% 15.19/2.49  --sig_cnt_out                           false
% 15.19/2.49  --trig_cnt_out                          false
% 15.19/2.49  --trig_cnt_out_tolerance                1.
% 15.19/2.49  --trig_cnt_out_sk_spl                   false
% 15.19/2.49  --abstr_cl_out                          false
% 15.19/2.49  
% 15.19/2.49  ------ Global Options
% 15.19/2.49  
% 15.19/2.49  --schedule                              default
% 15.19/2.49  --add_important_lit                     false
% 15.19/2.49  --prop_solver_per_cl                    1000
% 15.19/2.49  --min_unsat_core                        false
% 15.19/2.49  --soft_assumptions                      false
% 15.19/2.49  --soft_lemma_size                       3
% 15.19/2.49  --prop_impl_unit_size                   0
% 15.19/2.49  --prop_impl_unit                        []
% 15.19/2.49  --share_sel_clauses                     true
% 15.19/2.49  --reset_solvers                         false
% 15.19/2.49  --bc_imp_inh                            [conj_cone]
% 15.19/2.49  --conj_cone_tolerance                   3.
% 15.19/2.49  --extra_neg_conj                        none
% 15.19/2.49  --large_theory_mode                     true
% 15.19/2.49  --prolific_symb_bound                   200
% 15.19/2.49  --lt_threshold                          2000
% 15.19/2.49  --clause_weak_htbl                      true
% 15.19/2.49  --gc_record_bc_elim                     false
% 15.19/2.49  
% 15.19/2.49  ------ Preprocessing Options
% 15.19/2.49  
% 15.19/2.49  --preprocessing_flag                    true
% 15.19/2.49  --time_out_prep_mult                    0.1
% 15.19/2.49  --splitting_mode                        input
% 15.19/2.49  --splitting_grd                         true
% 15.19/2.49  --splitting_cvd                         false
% 15.19/2.49  --splitting_cvd_svl                     false
% 15.19/2.49  --splitting_nvd                         32
% 15.19/2.49  --sub_typing                            true
% 15.19/2.49  --prep_gs_sim                           true
% 15.19/2.49  --prep_unflatten                        true
% 15.19/2.49  --prep_res_sim                          true
% 15.19/2.49  --prep_upred                            true
% 15.19/2.49  --prep_sem_filter                       exhaustive
% 15.19/2.49  --prep_sem_filter_out                   false
% 15.19/2.49  --pred_elim                             true
% 15.19/2.49  --res_sim_input                         true
% 15.19/2.49  --eq_ax_congr_red                       true
% 15.19/2.49  --pure_diseq_elim                       true
% 15.19/2.49  --brand_transform                       false
% 15.19/2.49  --non_eq_to_eq                          false
% 15.19/2.49  --prep_def_merge                        true
% 15.19/2.49  --prep_def_merge_prop_impl              false
% 15.19/2.49  --prep_def_merge_mbd                    true
% 15.19/2.49  --prep_def_merge_tr_red                 false
% 15.19/2.49  --prep_def_merge_tr_cl                  false
% 15.19/2.49  --smt_preprocessing                     true
% 15.19/2.49  --smt_ac_axioms                         fast
% 15.19/2.49  --preprocessed_out                      false
% 15.19/2.49  --preprocessed_stats                    false
% 15.19/2.49  
% 15.19/2.49  ------ Abstraction refinement Options
% 15.19/2.49  
% 15.19/2.49  --abstr_ref                             []
% 15.19/2.49  --abstr_ref_prep                        false
% 15.19/2.49  --abstr_ref_until_sat                   false
% 15.19/2.49  --abstr_ref_sig_restrict                funpre
% 15.19/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.19/2.49  --abstr_ref_under                       []
% 15.19/2.49  
% 15.19/2.49  ------ SAT Options
% 15.19/2.49  
% 15.19/2.49  --sat_mode                              false
% 15.19/2.49  --sat_fm_restart_options                ""
% 15.19/2.49  --sat_gr_def                            false
% 15.19/2.49  --sat_epr_types                         true
% 15.19/2.49  --sat_non_cyclic_types                  false
% 15.19/2.49  --sat_finite_models                     false
% 15.19/2.49  --sat_fm_lemmas                         false
% 15.19/2.49  --sat_fm_prep                           false
% 15.19/2.49  --sat_fm_uc_incr                        true
% 15.19/2.49  --sat_out_model                         small
% 15.19/2.49  --sat_out_clauses                       false
% 15.19/2.49  
% 15.19/2.49  ------ QBF Options
% 15.19/2.49  
% 15.19/2.49  --qbf_mode                              false
% 15.19/2.49  --qbf_elim_univ                         false
% 15.19/2.49  --qbf_dom_inst                          none
% 15.19/2.49  --qbf_dom_pre_inst                      false
% 15.19/2.49  --qbf_sk_in                             false
% 15.19/2.49  --qbf_pred_elim                         true
% 15.19/2.49  --qbf_split                             512
% 15.19/2.49  
% 15.19/2.49  ------ BMC1 Options
% 15.19/2.49  
% 15.19/2.49  --bmc1_incremental                      false
% 15.19/2.49  --bmc1_axioms                           reachable_all
% 15.19/2.49  --bmc1_min_bound                        0
% 15.19/2.49  --bmc1_max_bound                        -1
% 15.19/2.49  --bmc1_max_bound_default                -1
% 15.19/2.49  --bmc1_symbol_reachability              true
% 15.19/2.49  --bmc1_property_lemmas                  false
% 15.19/2.49  --bmc1_k_induction                      false
% 15.19/2.49  --bmc1_non_equiv_states                 false
% 15.19/2.49  --bmc1_deadlock                         false
% 15.19/2.49  --bmc1_ucm                              false
% 15.19/2.49  --bmc1_add_unsat_core                   none
% 15.19/2.49  --bmc1_unsat_core_children              false
% 15.19/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.19/2.49  --bmc1_out_stat                         full
% 15.19/2.49  --bmc1_ground_init                      false
% 15.19/2.49  --bmc1_pre_inst_next_state              false
% 15.19/2.49  --bmc1_pre_inst_state                   false
% 15.19/2.49  --bmc1_pre_inst_reach_state             false
% 15.19/2.49  --bmc1_out_unsat_core                   false
% 15.19/2.49  --bmc1_aig_witness_out                  false
% 15.19/2.49  --bmc1_verbose                          false
% 15.19/2.49  --bmc1_dump_clauses_tptp                false
% 15.19/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.19/2.49  --bmc1_dump_file                        -
% 15.19/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.19/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.19/2.49  --bmc1_ucm_extend_mode                  1
% 15.19/2.49  --bmc1_ucm_init_mode                    2
% 15.19/2.49  --bmc1_ucm_cone_mode                    none
% 15.19/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.19/2.49  --bmc1_ucm_relax_model                  4
% 15.19/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.19/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.19/2.49  --bmc1_ucm_layered_model                none
% 15.19/2.49  --bmc1_ucm_max_lemma_size               10
% 15.19/2.49  
% 15.19/2.49  ------ AIG Options
% 15.19/2.49  
% 15.19/2.49  --aig_mode                              false
% 15.19/2.49  
% 15.19/2.49  ------ Instantiation Options
% 15.19/2.49  
% 15.19/2.49  --instantiation_flag                    true
% 15.19/2.49  --inst_sos_flag                         true
% 15.19/2.49  --inst_sos_phase                        true
% 15.19/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.19/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.19/2.49  --inst_lit_sel_side                     num_symb
% 15.19/2.49  --inst_solver_per_active                1400
% 15.19/2.49  --inst_solver_calls_frac                1.
% 15.19/2.49  --inst_passive_queue_type               priority_queues
% 15.19/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.19/2.49  --inst_passive_queues_freq              [25;2]
% 15.19/2.49  --inst_dismatching                      true
% 15.19/2.49  --inst_eager_unprocessed_to_passive     true
% 15.19/2.49  --inst_prop_sim_given                   true
% 15.19/2.49  --inst_prop_sim_new                     false
% 15.19/2.49  --inst_subs_new                         false
% 15.19/2.49  --inst_eq_res_simp                      false
% 15.19/2.49  --inst_subs_given                       false
% 15.19/2.49  --inst_orphan_elimination               true
% 15.19/2.49  --inst_learning_loop_flag               true
% 15.19/2.49  --inst_learning_start                   3000
% 15.19/2.49  --inst_learning_factor                  2
% 15.19/2.49  --inst_start_prop_sim_after_learn       3
% 15.19/2.49  --inst_sel_renew                        solver
% 15.19/2.49  --inst_lit_activity_flag                true
% 15.19/2.49  --inst_restr_to_given                   false
% 15.19/2.49  --inst_activity_threshold               500
% 15.19/2.49  --inst_out_proof                        true
% 15.19/2.49  
% 15.19/2.49  ------ Resolution Options
% 15.19/2.49  
% 15.19/2.49  --resolution_flag                       true
% 15.19/2.49  --res_lit_sel                           adaptive
% 15.19/2.49  --res_lit_sel_side                      none
% 15.19/2.49  --res_ordering                          kbo
% 15.19/2.49  --res_to_prop_solver                    active
% 15.19/2.49  --res_prop_simpl_new                    false
% 15.19/2.49  --res_prop_simpl_given                  true
% 15.19/2.49  --res_passive_queue_type                priority_queues
% 15.19/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.19/2.49  --res_passive_queues_freq               [15;5]
% 15.19/2.49  --res_forward_subs                      full
% 15.19/2.49  --res_backward_subs                     full
% 15.19/2.49  --res_forward_subs_resolution           true
% 15.19/2.49  --res_backward_subs_resolution          true
% 15.19/2.49  --res_orphan_elimination                true
% 15.19/2.49  --res_time_limit                        2.
% 15.19/2.49  --res_out_proof                         true
% 15.19/2.49  
% 15.19/2.49  ------ Superposition Options
% 15.19/2.49  
% 15.19/2.49  --superposition_flag                    true
% 15.19/2.49  --sup_passive_queue_type                priority_queues
% 15.19/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.19/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.19/2.49  --demod_completeness_check              fast
% 15.19/2.49  --demod_use_ground                      true
% 15.19/2.49  --sup_to_prop_solver                    passive
% 15.19/2.49  --sup_prop_simpl_new                    true
% 15.19/2.49  --sup_prop_simpl_given                  true
% 15.19/2.49  --sup_fun_splitting                     true
% 15.19/2.49  --sup_smt_interval                      50000
% 15.19/2.49  
% 15.19/2.49  ------ Superposition Simplification Setup
% 15.19/2.49  
% 15.19/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.19/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.19/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.19/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.19/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.19/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.19/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.19/2.49  --sup_immed_triv                        [TrivRules]
% 15.19/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.19/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.19/2.49  --sup_immed_bw_main                     []
% 15.19/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.19/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.19/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.19/2.49  --sup_input_bw                          []
% 15.19/2.49  
% 15.19/2.49  ------ Combination Options
% 15.19/2.49  
% 15.19/2.49  --comb_res_mult                         3
% 15.19/2.49  --comb_sup_mult                         2
% 15.19/2.49  --comb_inst_mult                        10
% 15.19/2.49  
% 15.19/2.49  ------ Debug Options
% 15.19/2.49  
% 15.19/2.49  --dbg_backtrace                         false
% 15.19/2.49  --dbg_dump_prop_clauses                 false
% 15.19/2.49  --dbg_dump_prop_clauses_file            -
% 15.19/2.49  --dbg_out_stat                          false
% 15.19/2.49  ------ Parsing...
% 15.19/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.19/2.49  
% 15.19/2.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 15.19/2.49  
% 15.19/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.19/2.49  
% 15.19/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.19/2.49  ------ Proving...
% 15.19/2.49  ------ Problem Properties 
% 15.19/2.49  
% 15.19/2.49  
% 15.19/2.49  clauses                                 25
% 15.19/2.49  conjectures                             3
% 15.19/2.49  EPR                                     4
% 15.19/2.49  Horn                                    22
% 15.19/2.49  unary                                   6
% 15.19/2.49  binary                                  10
% 15.19/2.49  lits                                    58
% 15.19/2.49  lits eq                                 25
% 15.19/2.49  fd_pure                                 0
% 15.19/2.49  fd_pseudo                               0
% 15.19/2.49  fd_cond                                 1
% 15.19/2.49  fd_pseudo_cond                          1
% 15.19/2.49  AC symbols                              0
% 15.19/2.49  
% 15.19/2.49  ------ Schedule dynamic 5 is on 
% 15.19/2.49  
% 15.19/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.19/2.49  
% 15.19/2.49  
% 15.19/2.49  ------ 
% 15.19/2.49  Current options:
% 15.19/2.49  ------ 
% 15.19/2.49  
% 15.19/2.49  ------ Input Options
% 15.19/2.49  
% 15.19/2.49  --out_options                           all
% 15.19/2.49  --tptp_safe_out                         true
% 15.19/2.49  --problem_path                          ""
% 15.19/2.49  --include_path                          ""
% 15.19/2.49  --clausifier                            res/vclausify_rel
% 15.19/2.49  --clausifier_options                    ""
% 15.19/2.49  --stdin                                 false
% 15.19/2.49  --stats_out                             all
% 15.19/2.49  
% 15.19/2.49  ------ General Options
% 15.19/2.49  
% 15.19/2.49  --fof                                   false
% 15.19/2.49  --time_out_real                         305.
% 15.19/2.49  --time_out_virtual                      -1.
% 15.19/2.49  --symbol_type_check                     false
% 15.19/2.49  --clausify_out                          false
% 15.19/2.49  --sig_cnt_out                           false
% 15.19/2.49  --trig_cnt_out                          false
% 15.19/2.49  --trig_cnt_out_tolerance                1.
% 15.19/2.49  --trig_cnt_out_sk_spl                   false
% 15.19/2.49  --abstr_cl_out                          false
% 15.19/2.49  
% 15.19/2.49  ------ Global Options
% 15.19/2.49  
% 15.19/2.49  --schedule                              default
% 15.19/2.49  --add_important_lit                     false
% 15.19/2.49  --prop_solver_per_cl                    1000
% 15.19/2.49  --min_unsat_core                        false
% 15.19/2.49  --soft_assumptions                      false
% 15.19/2.49  --soft_lemma_size                       3
% 15.19/2.49  --prop_impl_unit_size                   0
% 15.19/2.49  --prop_impl_unit                        []
% 15.19/2.49  --share_sel_clauses                     true
% 15.19/2.49  --reset_solvers                         false
% 15.19/2.49  --bc_imp_inh                            [conj_cone]
% 15.19/2.49  --conj_cone_tolerance                   3.
% 15.19/2.49  --extra_neg_conj                        none
% 15.19/2.49  --large_theory_mode                     true
% 15.19/2.49  --prolific_symb_bound                   200
% 15.19/2.49  --lt_threshold                          2000
% 15.19/2.49  --clause_weak_htbl                      true
% 15.19/2.49  --gc_record_bc_elim                     false
% 15.19/2.49  
% 15.19/2.49  ------ Preprocessing Options
% 15.19/2.49  
% 15.19/2.49  --preprocessing_flag                    true
% 15.19/2.49  --time_out_prep_mult                    0.1
% 15.19/2.49  --splitting_mode                        input
% 15.19/2.49  --splitting_grd                         true
% 15.19/2.49  --splitting_cvd                         false
% 15.19/2.49  --splitting_cvd_svl                     false
% 15.19/2.49  --splitting_nvd                         32
% 15.19/2.49  --sub_typing                            true
% 15.19/2.49  --prep_gs_sim                           true
% 15.19/2.49  --prep_unflatten                        true
% 15.19/2.49  --prep_res_sim                          true
% 15.19/2.49  --prep_upred                            true
% 15.19/2.49  --prep_sem_filter                       exhaustive
% 15.19/2.49  --prep_sem_filter_out                   false
% 15.19/2.49  --pred_elim                             true
% 15.19/2.49  --res_sim_input                         true
% 15.19/2.49  --eq_ax_congr_red                       true
% 15.19/2.49  --pure_diseq_elim                       true
% 15.19/2.49  --brand_transform                       false
% 15.19/2.49  --non_eq_to_eq                          false
% 15.19/2.49  --prep_def_merge                        true
% 15.19/2.49  --prep_def_merge_prop_impl              false
% 15.19/2.49  --prep_def_merge_mbd                    true
% 15.19/2.49  --prep_def_merge_tr_red                 false
% 15.19/2.49  --prep_def_merge_tr_cl                  false
% 15.19/2.49  --smt_preprocessing                     true
% 15.19/2.49  --smt_ac_axioms                         fast
% 15.19/2.49  --preprocessed_out                      false
% 15.19/2.49  --preprocessed_stats                    false
% 15.19/2.49  
% 15.19/2.49  ------ Abstraction refinement Options
% 15.19/2.49  
% 15.19/2.49  --abstr_ref                             []
% 15.19/2.49  --abstr_ref_prep                        false
% 15.19/2.49  --abstr_ref_until_sat                   false
% 15.19/2.49  --abstr_ref_sig_restrict                funpre
% 15.19/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.19/2.49  --abstr_ref_under                       []
% 15.19/2.49  
% 15.19/2.49  ------ SAT Options
% 15.19/2.49  
% 15.19/2.49  --sat_mode                              false
% 15.19/2.49  --sat_fm_restart_options                ""
% 15.19/2.49  --sat_gr_def                            false
% 15.19/2.49  --sat_epr_types                         true
% 15.19/2.49  --sat_non_cyclic_types                  false
% 15.19/2.49  --sat_finite_models                     false
% 15.19/2.49  --sat_fm_lemmas                         false
% 15.19/2.49  --sat_fm_prep                           false
% 15.19/2.49  --sat_fm_uc_incr                        true
% 15.19/2.49  --sat_out_model                         small
% 15.19/2.49  --sat_out_clauses                       false
% 15.19/2.49  
% 15.19/2.49  ------ QBF Options
% 15.19/2.49  
% 15.19/2.49  --qbf_mode                              false
% 15.19/2.49  --qbf_elim_univ                         false
% 15.19/2.49  --qbf_dom_inst                          none
% 15.19/2.49  --qbf_dom_pre_inst                      false
% 15.19/2.49  --qbf_sk_in                             false
% 15.19/2.49  --qbf_pred_elim                         true
% 15.19/2.49  --qbf_split                             512
% 15.19/2.49  
% 15.19/2.49  ------ BMC1 Options
% 15.19/2.49  
% 15.19/2.49  --bmc1_incremental                      false
% 15.19/2.49  --bmc1_axioms                           reachable_all
% 15.19/2.49  --bmc1_min_bound                        0
% 15.19/2.49  --bmc1_max_bound                        -1
% 15.19/2.49  --bmc1_max_bound_default                -1
% 15.19/2.49  --bmc1_symbol_reachability              true
% 15.19/2.49  --bmc1_property_lemmas                  false
% 15.19/2.49  --bmc1_k_induction                      false
% 15.19/2.49  --bmc1_non_equiv_states                 false
% 15.19/2.49  --bmc1_deadlock                         false
% 15.19/2.49  --bmc1_ucm                              false
% 15.19/2.49  --bmc1_add_unsat_core                   none
% 15.19/2.49  --bmc1_unsat_core_children              false
% 15.19/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.19/2.49  --bmc1_out_stat                         full
% 15.19/2.49  --bmc1_ground_init                      false
% 15.19/2.49  --bmc1_pre_inst_next_state              false
% 15.19/2.49  --bmc1_pre_inst_state                   false
% 15.19/2.49  --bmc1_pre_inst_reach_state             false
% 15.19/2.49  --bmc1_out_unsat_core                   false
% 15.19/2.49  --bmc1_aig_witness_out                  false
% 15.19/2.49  --bmc1_verbose                          false
% 15.19/2.49  --bmc1_dump_clauses_tptp                false
% 15.19/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.19/2.49  --bmc1_dump_file                        -
% 15.19/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.19/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.19/2.49  --bmc1_ucm_extend_mode                  1
% 15.19/2.49  --bmc1_ucm_init_mode                    2
% 15.19/2.49  --bmc1_ucm_cone_mode                    none
% 15.19/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.19/2.49  --bmc1_ucm_relax_model                  4
% 15.19/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.19/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.19/2.49  --bmc1_ucm_layered_model                none
% 15.19/2.49  --bmc1_ucm_max_lemma_size               10
% 15.19/2.49  
% 15.19/2.49  ------ AIG Options
% 15.19/2.49  
% 15.19/2.49  --aig_mode                              false
% 15.19/2.49  
% 15.19/2.49  ------ Instantiation Options
% 15.19/2.49  
% 15.19/2.49  --instantiation_flag                    true
% 15.19/2.49  --inst_sos_flag                         true
% 15.19/2.49  --inst_sos_phase                        true
% 15.19/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.19/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.19/2.49  --inst_lit_sel_side                     none
% 15.19/2.49  --inst_solver_per_active                1400
% 15.19/2.49  --inst_solver_calls_frac                1.
% 15.19/2.49  --inst_passive_queue_type               priority_queues
% 15.19/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.19/2.49  --inst_passive_queues_freq              [25;2]
% 15.19/2.49  --inst_dismatching                      true
% 15.19/2.49  --inst_eager_unprocessed_to_passive     true
% 15.19/2.49  --inst_prop_sim_given                   true
% 15.19/2.49  --inst_prop_sim_new                     false
% 15.19/2.49  --inst_subs_new                         false
% 15.19/2.49  --inst_eq_res_simp                      false
% 15.19/2.49  --inst_subs_given                       false
% 15.19/2.49  --inst_orphan_elimination               true
% 15.19/2.49  --inst_learning_loop_flag               true
% 15.19/2.49  --inst_learning_start                   3000
% 15.19/2.49  --inst_learning_factor                  2
% 15.19/2.49  --inst_start_prop_sim_after_learn       3
% 15.19/2.49  --inst_sel_renew                        solver
% 15.19/2.49  --inst_lit_activity_flag                true
% 15.19/2.49  --inst_restr_to_given                   false
% 15.19/2.49  --inst_activity_threshold               500
% 15.19/2.49  --inst_out_proof                        true
% 15.19/2.49  
% 15.19/2.49  ------ Resolution Options
% 15.19/2.49  
% 15.19/2.49  --resolution_flag                       false
% 15.19/2.49  --res_lit_sel                           adaptive
% 15.19/2.49  --res_lit_sel_side                      none
% 15.19/2.49  --res_ordering                          kbo
% 15.19/2.49  --res_to_prop_solver                    active
% 15.19/2.49  --res_prop_simpl_new                    false
% 15.19/2.49  --res_prop_simpl_given                  true
% 15.19/2.49  --res_passive_queue_type                priority_queues
% 15.19/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.19/2.49  --res_passive_queues_freq               [15;5]
% 15.19/2.49  --res_forward_subs                      full
% 15.19/2.49  --res_backward_subs                     full
% 15.19/2.49  --res_forward_subs_resolution           true
% 15.19/2.49  --res_backward_subs_resolution          true
% 15.19/2.49  --res_orphan_elimination                true
% 15.19/2.49  --res_time_limit                        2.
% 15.19/2.49  --res_out_proof                         true
% 15.19/2.49  
% 15.19/2.49  ------ Superposition Options
% 15.19/2.49  
% 15.19/2.49  --superposition_flag                    true
% 15.19/2.49  --sup_passive_queue_type                priority_queues
% 15.19/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.19/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.19/2.49  --demod_completeness_check              fast
% 15.19/2.49  --demod_use_ground                      true
% 15.19/2.49  --sup_to_prop_solver                    passive
% 15.19/2.49  --sup_prop_simpl_new                    true
% 15.19/2.49  --sup_prop_simpl_given                  true
% 15.19/2.49  --sup_fun_splitting                     true
% 15.19/2.49  --sup_smt_interval                      50000
% 15.19/2.49  
% 15.19/2.49  ------ Superposition Simplification Setup
% 15.19/2.49  
% 15.19/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.19/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.19/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.19/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.19/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.19/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.19/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.19/2.49  --sup_immed_triv                        [TrivRules]
% 15.19/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.19/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.19/2.49  --sup_immed_bw_main                     []
% 15.19/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.19/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.19/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.19/2.49  --sup_input_bw                          []
% 15.19/2.49  
% 15.19/2.49  ------ Combination Options
% 15.19/2.49  
% 15.19/2.49  --comb_res_mult                         3
% 15.19/2.49  --comb_sup_mult                         2
% 15.19/2.49  --comb_inst_mult                        10
% 15.19/2.49  
% 15.19/2.49  ------ Debug Options
% 15.19/2.49  
% 15.19/2.49  --dbg_backtrace                         false
% 15.19/2.49  --dbg_dump_prop_clauses                 false
% 15.19/2.49  --dbg_dump_prop_clauses_file            -
% 15.19/2.49  --dbg_out_stat                          false
% 15.19/2.49  
% 15.19/2.49  
% 15.19/2.49  
% 15.19/2.49  
% 15.19/2.49  ------ Proving...
% 15.19/2.49  
% 15.19/2.49  
% 15.19/2.49  % SZS status Theorem for theBenchmark.p
% 15.19/2.49  
% 15.19/2.49   Resolution empty clause
% 15.19/2.49  
% 15.19/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.19/2.49  
% 15.19/2.49  fof(f7,axiom,(
% 15.19/2.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 15.19/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f52,plain,(
% 15.19/2.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f7])).
% 15.19/2.49  
% 15.19/2.49  fof(f13,axiom,(
% 15.19/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 15.19/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f25,plain,(
% 15.19/2.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.19/2.49    inference(ennf_transformation,[],[f13])).
% 15.19/2.49  
% 15.19/2.49  fof(f26,plain,(
% 15.19/2.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.19/2.49    inference(flattening,[],[f25])).
% 15.19/2.49  
% 15.19/2.49  fof(f36,plain,(
% 15.19/2.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.19/2.49    inference(nnf_transformation,[],[f26])).
% 15.19/2.49  
% 15.19/2.49  fof(f59,plain,(
% 15.19/2.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f36])).
% 15.19/2.49  
% 15.19/2.49  fof(f14,conjecture,(
% 15.19/2.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 15.19/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f15,negated_conjecture,(
% 15.19/2.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 15.19/2.49    inference(negated_conjecture,[],[f14])).
% 15.19/2.49  
% 15.19/2.49  fof(f27,plain,(
% 15.19/2.49    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 15.19/2.49    inference(ennf_transformation,[],[f15])).
% 15.19/2.49  
% 15.19/2.49  fof(f28,plain,(
% 15.19/2.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 15.19/2.49    inference(flattening,[],[f27])).
% 15.19/2.49  
% 15.19/2.49  fof(f37,plain,(
% 15.19/2.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 15.19/2.49    introduced(choice_axiom,[])).
% 15.19/2.49  
% 15.19/2.49  fof(f38,plain,(
% 15.19/2.49    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 15.19/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f37])).
% 15.19/2.49  
% 15.19/2.49  fof(f66,plain,(
% 15.19/2.49    v1_funct_2(sK3,sK0,sK1)),
% 15.19/2.49    inference(cnf_transformation,[],[f38])).
% 15.19/2.49  
% 15.19/2.49  fof(f67,plain,(
% 15.19/2.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 15.19/2.49    inference(cnf_transformation,[],[f38])).
% 15.19/2.49  
% 15.19/2.49  fof(f10,axiom,(
% 15.19/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 15.19/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f21,plain,(
% 15.19/2.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.19/2.49    inference(ennf_transformation,[],[f10])).
% 15.19/2.49  
% 15.19/2.49  fof(f56,plain,(
% 15.19/2.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f21])).
% 15.19/2.49  
% 15.19/2.49  fof(f9,axiom,(
% 15.19/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 15.19/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f20,plain,(
% 15.19/2.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.19/2.49    inference(ennf_transformation,[],[f9])).
% 15.19/2.49  
% 15.19/2.49  fof(f54,plain,(
% 15.19/2.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f20])).
% 15.19/2.49  
% 15.19/2.49  fof(f5,axiom,(
% 15.19/2.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 15.19/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f17,plain,(
% 15.19/2.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 15.19/2.49    inference(ennf_transformation,[],[f5])).
% 15.19/2.49  
% 15.19/2.49  fof(f34,plain,(
% 15.19/2.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 15.19/2.49    inference(nnf_transformation,[],[f17])).
% 15.19/2.49  
% 15.19/2.49  fof(f48,plain,(
% 15.19/2.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f34])).
% 15.19/2.49  
% 15.19/2.49  fof(f8,axiom,(
% 15.19/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 15.19/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f19,plain,(
% 15.19/2.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.19/2.49    inference(ennf_transformation,[],[f8])).
% 15.19/2.49  
% 15.19/2.49  fof(f53,plain,(
% 15.19/2.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f19])).
% 15.19/2.49  
% 15.19/2.49  fof(f11,axiom,(
% 15.19/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 15.19/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f22,plain,(
% 15.19/2.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.19/2.49    inference(ennf_transformation,[],[f11])).
% 15.19/2.49  
% 15.19/2.49  fof(f57,plain,(
% 15.19/2.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f22])).
% 15.19/2.49  
% 15.19/2.49  fof(f68,plain,(
% 15.19/2.49    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 15.19/2.49    inference(cnf_transformation,[],[f38])).
% 15.19/2.49  
% 15.19/2.49  fof(f12,axiom,(
% 15.19/2.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.19/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f23,plain,(
% 15.19/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 15.19/2.49    inference(ennf_transformation,[],[f12])).
% 15.19/2.49  
% 15.19/2.49  fof(f24,plain,(
% 15.19/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 15.19/2.49    inference(flattening,[],[f23])).
% 15.19/2.49  
% 15.19/2.49  fof(f58,plain,(
% 15.19/2.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f24])).
% 15.19/2.49  
% 15.19/2.49  fof(f61,plain,(
% 15.19/2.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f36])).
% 15.19/2.49  
% 15.19/2.49  fof(f70,plain,(
% 15.19/2.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 15.19/2.49    inference(cnf_transformation,[],[f38])).
% 15.19/2.49  
% 15.19/2.49  fof(f65,plain,(
% 15.19/2.49    v1_funct_1(sK3)),
% 15.19/2.49    inference(cnf_transformation,[],[f38])).
% 15.19/2.49  
% 15.19/2.49  fof(f2,axiom,(
% 15.19/2.49    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.19/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f31,plain,(
% 15.19/2.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 15.19/2.49    inference(nnf_transformation,[],[f2])).
% 15.19/2.49  
% 15.19/2.49  fof(f32,plain,(
% 15.19/2.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 15.19/2.49    inference(flattening,[],[f31])).
% 15.19/2.49  
% 15.19/2.49  fof(f42,plain,(
% 15.19/2.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 15.19/2.49    inference(cnf_transformation,[],[f32])).
% 15.19/2.49  
% 15.19/2.49  fof(f43,plain,(
% 15.19/2.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 15.19/2.49    inference(cnf_transformation,[],[f32])).
% 15.19/2.49  
% 15.19/2.49  fof(f74,plain,(
% 15.19/2.49    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 15.19/2.49    inference(equality_resolution,[],[f43])).
% 15.19/2.49  
% 15.19/2.49  fof(f1,axiom,(
% 15.19/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.19/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f29,plain,(
% 15.19/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.19/2.49    inference(nnf_transformation,[],[f1])).
% 15.19/2.49  
% 15.19/2.49  fof(f30,plain,(
% 15.19/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.19/2.49    inference(flattening,[],[f29])).
% 15.19/2.49  
% 15.19/2.49  fof(f39,plain,(
% 15.19/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.19/2.49    inference(cnf_transformation,[],[f30])).
% 15.19/2.49  
% 15.19/2.49  fof(f72,plain,(
% 15.19/2.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.19/2.49    inference(equality_resolution,[],[f39])).
% 15.19/2.49  
% 15.19/2.49  fof(f63,plain,(
% 15.19/2.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f36])).
% 15.19/2.49  
% 15.19/2.49  fof(f77,plain,(
% 15.19/2.49    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 15.19/2.49    inference(equality_resolution,[],[f63])).
% 15.19/2.49  
% 15.19/2.49  fof(f44,plain,(
% 15.19/2.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 15.19/2.49    inference(cnf_transformation,[],[f32])).
% 15.19/2.49  
% 15.19/2.49  fof(f73,plain,(
% 15.19/2.49    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 15.19/2.49    inference(equality_resolution,[],[f44])).
% 15.19/2.49  
% 15.19/2.49  fof(f69,plain,(
% 15.19/2.49    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 15.19/2.49    inference(cnf_transformation,[],[f38])).
% 15.19/2.49  
% 15.19/2.49  fof(f55,plain,(
% 15.19/2.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f20])).
% 15.19/2.49  
% 15.19/2.49  fof(f6,axiom,(
% 15.19/2.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 15.19/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f18,plain,(
% 15.19/2.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 15.19/2.49    inference(ennf_transformation,[],[f6])).
% 15.19/2.49  
% 15.19/2.49  fof(f35,plain,(
% 15.19/2.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 15.19/2.49    inference(nnf_transformation,[],[f18])).
% 15.19/2.49  
% 15.19/2.49  fof(f50,plain,(
% 15.19/2.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f35])).
% 15.19/2.49  
% 15.19/2.49  fof(f3,axiom,(
% 15.19/2.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.19/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f33,plain,(
% 15.19/2.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.19/2.49    inference(nnf_transformation,[],[f3])).
% 15.19/2.49  
% 15.19/2.49  fof(f45,plain,(
% 15.19/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f33])).
% 15.19/2.49  
% 15.19/2.49  fof(f46,plain,(
% 15.19/2.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f33])).
% 15.19/2.49  
% 15.19/2.49  fof(f41,plain,(
% 15.19/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f30])).
% 15.19/2.49  
% 15.19/2.49  fof(f60,plain,(
% 15.19/2.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f36])).
% 15.19/2.49  
% 15.19/2.49  fof(f79,plain,(
% 15.19/2.49    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 15.19/2.49    inference(equality_resolution,[],[f60])).
% 15.19/2.49  
% 15.19/2.49  fof(f4,axiom,(
% 15.19/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 15.19/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.19/2.49  
% 15.19/2.49  fof(f16,plain,(
% 15.19/2.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 15.19/2.49    inference(ennf_transformation,[],[f4])).
% 15.19/2.49  
% 15.19/2.49  fof(f47,plain,(
% 15.19/2.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 15.19/2.49    inference(cnf_transformation,[],[f16])).
% 15.19/2.49  
% 15.19/2.49  fof(f62,plain,(
% 15.19/2.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.19/2.49    inference(cnf_transformation,[],[f36])).
% 15.19/2.49  
% 15.19/2.49  fof(f78,plain,(
% 15.19/2.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 15.19/2.49    inference(equality_resolution,[],[f62])).
% 15.19/2.49  
% 15.19/2.49  cnf(c_13,plain,
% 15.19/2.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 15.19/2.49      inference(cnf_transformation,[],[f52]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1251,plain,
% 15.19/2.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_25,plain,
% 15.19/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.19/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.19/2.49      | k1_relset_1(X1,X2,X0) = X1
% 15.19/2.49      | k1_xboole_0 = X2 ),
% 15.19/2.49      inference(cnf_transformation,[],[f59]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_30,negated_conjecture,
% 15.19/2.49      ( v1_funct_2(sK3,sK0,sK1) ),
% 15.19/2.49      inference(cnf_transformation,[],[f66]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_513,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.19/2.49      | k1_relset_1(X1,X2,X0) = X1
% 15.19/2.49      | sK1 != X2
% 15.19/2.49      | sK0 != X1
% 15.19/2.49      | sK3 != X0
% 15.19/2.49      | k1_xboole_0 = X2 ),
% 15.19/2.49      inference(resolution_lifted,[status(thm)],[c_25,c_30]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_514,plain,
% 15.19/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.19/2.49      | k1_relset_1(sK0,sK1,sK3) = sK0
% 15.19/2.49      | k1_xboole_0 = sK1 ),
% 15.19/2.49      inference(unflattening,[status(thm)],[c_513]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_29,negated_conjecture,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 15.19/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_516,plain,
% 15.19/2.49      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 15.19/2.49      inference(global_propositional_subsumption,[status(thm)],[c_514,c_29]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1245,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.19/2.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.19/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1249,plain,
% 15.19/2.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.19/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_3590,plain,
% 15.19/2.49      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1245,c_1249]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_3975,plain,
% 15.19/2.49      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_516,c_3590]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_16,plain,
% 15.19/2.49      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 15.19/2.49      inference(cnf_transformation,[],[f54]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_10,plain,
% 15.19/2.49      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 15.19/2.49      inference(cnf_transformation,[],[f48]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_378,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.19/2.49      | r1_tarski(k1_relat_1(X0),X1)
% 15.19/2.49      | ~ v1_relat_1(X0) ),
% 15.19/2.49      inference(resolution,[status(thm)],[c_16,c_10]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_14,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 15.19/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_382,plain,
% 15.19/2.49      ( r1_tarski(k1_relat_1(X0),X1)
% 15.19/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 15.19/2.49      inference(global_propositional_subsumption,[status(thm)],[c_378,c_14]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_383,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.19/2.49      | r1_tarski(k1_relat_1(X0),X1) ),
% 15.19/2.49      inference(renaming,[status(thm)],[c_382]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1243,plain,
% 15.19/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.19/2.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2063,plain,
% 15.19/2.49      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1245,c_1243]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_18,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.19/2.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 15.19/2.49      inference(cnf_transformation,[],[f57]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1248,plain,
% 15.19/2.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 15.19/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2667,plain,
% 15.19/2.49      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1245,c_1248]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_28,negated_conjecture,
% 15.19/2.49      ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
% 15.19/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1246,plain,
% 15.19/2.49      ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2750,plain,
% 15.19/2.49      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 15.19/2.49      inference(demodulation,[status(thm)],[c_2667,c_1246]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_19,plain,
% 15.19/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.19/2.49      | ~ r1_tarski(k2_relat_1(X0),X2)
% 15.19/2.49      | ~ r1_tarski(k1_relat_1(X0),X1)
% 15.19/2.49      | ~ v1_relat_1(X0) ),
% 15.19/2.49      inference(cnf_transformation,[],[f58]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1247,plain,
% 15.19/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 15.19/2.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 15.19/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_3589,plain,
% 15.19/2.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.19/2.49      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 15.19/2.49      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 15.19/2.49      | v1_relat_1(X2) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1247,c_1249]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17239,plain,
% 15.19/2.49      ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
% 15.19/2.49      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 15.19/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_2750,c_3589]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_34,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1327,plain,
% 15.19/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK3) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_14]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1392,plain,
% 15.19/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.19/2.49      | v1_relat_1(sK3) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1327]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1393,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.19/2.49      | v1_relat_1(sK3) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_1392]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17817,plain,
% 15.19/2.49      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 15.19/2.49      | k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3) ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_17239,c_34,c_1393]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17818,plain,
% 15.19/2.49      ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
% 15.19/2.49      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 15.19/2.49      inference(renaming,[status(thm)],[c_17817]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17826,plain,
% 15.19/2.49      ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_2063,c_17818]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_23,plain,
% 15.19/2.49      ( v1_funct_2(X0,X1,X2)
% 15.19/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.19/2.49      | k1_relset_1(X1,X2,X0) != X1
% 15.19/2.49      | k1_xboole_0 = X2 ),
% 15.19/2.49      inference(cnf_transformation,[],[f61]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_26,negated_conjecture,
% 15.19/2.49      ( ~ v1_funct_2(sK3,sK0,sK2)
% 15.19/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 15.19/2.49      | ~ v1_funct_1(sK3) ),
% 15.19/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_31,negated_conjecture,
% 15.19/2.49      ( v1_funct_1(sK3) ),
% 15.19/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_165,plain,
% 15.19/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 15.19/2.49      | ~ v1_funct_2(sK3,sK0,sK2) ),
% 15.19/2.49      inference(global_propositional_subsumption,[status(thm)],[c_26,c_31]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_166,negated_conjecture,
% 15.19/2.49      ( ~ v1_funct_2(sK3,sK0,sK2)
% 15.19/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 15.19/2.49      inference(renaming,[status(thm)],[c_165]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_500,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.19/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 15.19/2.49      | k1_relset_1(X1,X2,X0) != X1
% 15.19/2.49      | sK2 != X2
% 15.19/2.49      | sK0 != X1
% 15.19/2.49      | sK3 != X0
% 15.19/2.49      | k1_xboole_0 = X2 ),
% 15.19/2.49      inference(resolution_lifted,[status(thm)],[c_23,c_166]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_501,plain,
% 15.19/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 15.19/2.49      | k1_relset_1(sK0,sK2,sK3) != sK0
% 15.19/2.49      | k1_xboole_0 = sK2 ),
% 15.19/2.49      inference(unflattening,[status(thm)],[c_500]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1237,plain,
% 15.19/2.49      ( k1_relset_1(sK0,sK2,sK3) != sK0
% 15.19/2.49      | k1_xboole_0 = sK2
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17922,plain,
% 15.19/2.49      ( k1_relat_1(sK3) != sK0
% 15.19/2.49      | sK2 = k1_xboole_0
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 15.19/2.49      inference(demodulation,[status(thm)],[c_17826,c_1237]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1297,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 15.19/2.49      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 15.19/2.49      | ~ r1_tarski(k1_relat_1(sK3),sK0)
% 15.19/2.49      | ~ v1_relat_1(sK3) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_19]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1298,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 15.19/2.49      | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
% 15.19/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_1297]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17925,plain,
% 15.19/2.49      ( sK2 = k1_xboole_0 | k1_relat_1(sK3) != sK0 ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_17922,c_34,c_1298,c_1393,c_2063,c_2750]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17926,plain,
% 15.19/2.49      ( k1_relat_1(sK3) != sK0 | sK2 = k1_xboole_0 ),
% 15.19/2.49      inference(renaming,[status(thm)],[c_17925]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17927,plain,
% 15.19/2.49      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_3975,c_17926]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_5,plain,
% 15.19/2.49      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 15.19/2.49      | k1_xboole_0 = X1
% 15.19/2.49      | k1_xboole_0 = X0 ),
% 15.19/2.49      inference(cnf_transformation,[],[f42]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_95,plain,
% 15.19/2.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 15.19/2.49      | k1_xboole_0 = k1_xboole_0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_5]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_4,plain,
% 15.19/2.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.19/2.49      inference(cnf_transformation,[],[f74]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_96,plain,
% 15.19/2.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_4]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f72]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_98,plain,
% 15.19/2.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_2]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_763,plain,
% 15.19/2.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.19/2.49      theory(equality) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1314,plain,
% 15.19/2.49      ( ~ r1_tarski(X0,X1)
% 15.19/2.49      | r1_tarski(sK0,k1_xboole_0)
% 15.19/2.49      | sK0 != X0
% 15.19/2.49      | k1_xboole_0 != X1 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_763]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1316,plain,
% 15.19/2.49      ( r1_tarski(sK0,k1_xboole_0)
% 15.19/2.49      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 15.19/2.49      | sK0 != k1_xboole_0
% 15.19/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1314]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_21,plain,
% 15.19/2.49      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 15.19/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 15.19/2.49      | k1_xboole_0 = X1
% 15.19/2.49      | k1_xboole_0 = X0 ),
% 15.19/2.49      inference(cnf_transformation,[],[f77]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_451,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 15.19/2.49      | sK1 != k1_xboole_0
% 15.19/2.49      | sK0 != X1
% 15.19/2.49      | sK3 != X0
% 15.19/2.49      | k1_xboole_0 = X1
% 15.19/2.49      | k1_xboole_0 = X0 ),
% 15.19/2.49      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_452,plain,
% 15.19/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 15.19/2.49      | sK1 != k1_xboole_0
% 15.19/2.49      | k1_xboole_0 = sK0
% 15.19/2.49      | k1_xboole_0 = sK3 ),
% 15.19/2.49      inference(unflattening,[status(thm)],[c_451]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1240,plain,
% 15.19/2.49      ( sK1 != k1_xboole_0
% 15.19/2.49      | k1_xboole_0 = sK0
% 15.19/2.49      | k1_xboole_0 = sK3
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_3,plain,
% 15.19/2.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.19/2.49      inference(cnf_transformation,[],[f73]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1257,plain,
% 15.19/2.49      ( sK1 != k1_xboole_0
% 15.19/2.49      | sK0 = k1_xboole_0
% 15.19/2.49      | sK3 = k1_xboole_0
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.19/2.49      inference(demodulation,[status(thm)],[c_1240,c_3]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_27,negated_conjecture,
% 15.19/2.49      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 15.19/2.49      inference(cnf_transformation,[],[f69]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_762,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1291,plain,
% 15.19/2.49      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_762]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1352,plain,
% 15.19/2.49      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1291]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_761,plain,( X0 = X0 ),theory(equality) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1482,plain,
% 15.19/2.49      ( sK0 = sK0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_761]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1817,plain,
% 15.19/2.49      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_762]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1818,plain,
% 15.19/2.49      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1817]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1866,plain,
% 15.19/2.49      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_1257,c_27,c_95,c_96,c_1352,c_1482,c_1818]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1885,plain,
% 15.19/2.49      ( X0 != X1 | X0 = sK0 | sK0 != X1 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_762]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_4507,plain,
% 15.19/2.49      ( k1_relat_1(sK3) != X0 | k1_relat_1(sK3) = sK0 | sK0 != X0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1885]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_4515,plain,
% 15.19/2.49      ( k1_relat_1(sK3) = sK0
% 15.19/2.49      | k1_relat_1(sK3) != k1_xboole_0
% 15.19/2.49      | sK0 != k1_xboole_0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_4507]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_3365,plain,
% 15.19/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 15.19/2.49      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 15.19/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_4,c_1247]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_4498,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.19/2.49      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 15.19/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_2750,c_3365]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_4978,plain,
% 15.19/2.49      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_4498,c_34,c_1393]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_4979,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.19/2.49      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 15.19/2.49      inference(renaming,[status(thm)],[c_4978]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_4983,plain,
% 15.19/2.49      ( sK1 = k1_xboole_0
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.19/2.49      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_3975,c_4979]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1485,plain,
% 15.19/2.49      ( sK3 = sK3 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_761]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_15,plain,
% 15.19/2.49      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 15.19/2.49      inference(cnf_transformation,[],[f55]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_12,plain,
% 15.19/2.49      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 15.19/2.49      inference(cnf_transformation,[],[f50]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_399,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.19/2.49      | r1_tarski(k2_relat_1(X0),X2)
% 15.19/2.49      | ~ v1_relat_1(X0) ),
% 15.19/2.49      inference(resolution,[status(thm)],[c_15,c_12]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_403,plain,
% 15.19/2.49      ( r1_tarski(k2_relat_1(X0),X2)
% 15.19/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 15.19/2.49      inference(global_propositional_subsumption,[status(thm)],[c_399,c_14]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_404,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.19/2.49      | r1_tarski(k2_relat_1(X0),X2) ),
% 15.19/2.49      inference(renaming,[status(thm)],[c_403]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1616,plain,
% 15.19/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.19/2.49      | r1_tarski(k2_relat_1(sK3),X1) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_404]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1617,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(sK3),X1) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_1616]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1619,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) = iProver_top ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1617]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_766,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.19/2.49      theory(equality) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1448,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,X1)
% 15.19/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 15.19/2.49      | X2 != X0
% 15.19/2.49      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != X1 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_766]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1687,plain,
% 15.19/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.19/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.19/2.49      | X0 != sK3
% 15.19/2.49      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1448]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1730,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.19/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.19/2.49      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 15.19/2.49      | sK3 != sK3 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1687]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1731,plain,
% 15.19/2.49      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 15.19/2.49      | sK3 != sK3
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_1730]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1733,plain,
% 15.19/2.49      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 15.19/2.49      | sK3 != sK3
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1731]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_765,plain,
% 15.19/2.49      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 15.19/2.49      theory(equality) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1781,plain,
% 15.19/2.49      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
% 15.19/2.49      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_765]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1782,plain,
% 15.19/2.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK0,sK1)
% 15.19/2.49      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1781]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_764,plain,
% 15.19/2.49      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 15.19/2.49      theory(equality) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2356,plain,
% 15.19/2.49      ( X0 != sK1 | X1 != sK0 | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK0,sK1) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_764]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2357,plain,
% 15.19/2.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK0,sK1)
% 15.19/2.49      | k1_xboole_0 != sK1
% 15.19/2.49      | k1_xboole_0 != sK0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_2356]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_3364,plain,
% 15.19/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 15.19/2.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 15.19/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_3,c_1247]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_4407,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 15.19/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_2063,c_3364]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_5050,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.19/2.49      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_4983,c_34,c_27,c_95,c_96,c_1393,c_1485,c_1619,c_1733,
% 15.19/2.49                 c_1782,c_1818,c_2357,c_4407]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_5052,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 15.19/2.49      | ~ r1_tarski(sK0,k1_xboole_0) ),
% 15.19/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_5050]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1242,plain,
% 15.19/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1640,plain,
% 15.19/2.49      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1245,c_1242]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17241,plain,
% 15.19/2.49      ( k1_relset_1(X0,sK1,sK3) = k1_relat_1(sK3)
% 15.19/2.49      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 15.19/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1640,c_3589]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_7,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.19/2.49      inference(cnf_transformation,[],[f45]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1847,plain,
% 15.19/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_7]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1848,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 15.19/2.49      | r1_tarski(sK3,X0) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_1847]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1850,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.19/2.49      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1848]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1981,plain,
% 15.19/2.49      ( r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3)) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_2]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_3888,plain,
% 15.19/2.49      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_762]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_3889,plain,
% 15.19/2.49      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_3888]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_6,plain,
% 15.19/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.19/2.49      inference(cnf_transformation,[],[f46]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1253,plain,
% 15.19/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 15.19/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2064,plain,
% 15.19/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.19/2.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_3,c_1243]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2569,plain,
% 15.19/2.49      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 15.19/2.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1253,c_2064]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_3977,plain,
% 15.19/2.49      ( sK1 = k1_xboole_0
% 15.19/2.49      | r1_tarski(sK0,X0) = iProver_top
% 15.19/2.49      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_3975,c_2569]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_3981,plain,
% 15.19/2.49      ( sK1 = k1_xboole_0
% 15.19/2.49      | r1_tarski(sK0,k1_xboole_0) = iProver_top
% 15.19/2.49      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_3977]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_5055,plain,
% 15.19/2.49      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 15.19/2.49      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_5050,c_2064]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_5063,plain,
% 15.19/2.49      ( r1_tarski(k1_relat_1(sK3),X0) | ~ r1_tarski(sK0,k1_xboole_0) ),
% 15.19/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_5055]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_0,plain,
% 15.19/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.19/2.49      inference(cnf_transformation,[],[f41]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2022,plain,
% 15.19/2.49      ( ~ r1_tarski(X0,k2_relat_1(sK3))
% 15.19/2.49      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 15.19/2.49      | k2_relat_1(sK3) = X0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_0]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_6128,plain,
% 15.19/2.49      ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
% 15.19/2.49      | k2_relat_1(sK3) = k2_relat_1(sK3) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_2022]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1621,plain,
% 15.19/2.49      ( ~ r1_tarski(X0,X1)
% 15.19/2.49      | r1_tarski(k2_relat_1(sK3),X2)
% 15.19/2.49      | X2 != X1
% 15.19/2.49      | k2_relat_1(sK3) != X0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_763]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2027,plain,
% 15.19/2.49      ( ~ r1_tarski(k2_relat_1(sK3),X0)
% 15.19/2.49      | r1_tarski(k2_relat_1(sK3),X1)
% 15.19/2.49      | X1 != X0
% 15.19/2.49      | k2_relat_1(sK3) != k2_relat_1(sK3) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1621]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_10824,plain,
% 15.19/2.49      ( r1_tarski(k2_relat_1(sK3),X0)
% 15.19/2.49      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 15.19/2.49      | X0 != sK2
% 15.19/2.49      | k2_relat_1(sK3) != k2_relat_1(sK3) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_2027]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_10825,plain,
% 15.19/2.49      ( X0 != sK2
% 15.19/2.49      | k2_relat_1(sK3) != k2_relat_1(sK3)
% 15.19/2.49      | r1_tarski(k2_relat_1(sK3),X0) = iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_10824]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_10827,plain,
% 15.19/2.49      ( k2_relat_1(sK3) != k2_relat_1(sK3)
% 15.19/2.49      | k1_xboole_0 != sK2
% 15.19/2.49      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) = iProver_top ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_10825]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17267,plain,
% 15.19/2.49      ( ~ r1_tarski(k1_relat_1(sK3),X0)
% 15.19/2.49      | ~ v1_relat_1(sK3)
% 15.19/2.49      | k1_relset_1(X0,sK1,sK3) = k1_relat_1(sK3) ),
% 15.19/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_17241]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17976,plain,
% 15.19/2.49      ( k1_relset_1(X0,sK1,sK3) = k1_relat_1(sK3) ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_17241,c_29,c_34,c_95,c_96,c_98,c_1316,c_1392,c_1393,
% 15.19/2.49                 c_1850,c_1866,c_1981,c_2750,c_3889,c_3981,c_4407,c_5055,
% 15.19/2.49                 c_5063,c_6128,c_10827,c_17267,c_17927]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_24,plain,
% 15.19/2.49      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 15.19/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 15.19/2.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 15.19/2.49      inference(cnf_transformation,[],[f79]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_487,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 15.19/2.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 15.19/2.49      | sK1 != X1
% 15.19/2.49      | sK0 != k1_xboole_0
% 15.19/2.49      | sK3 != X0 ),
% 15.19/2.49      inference(resolution_lifted,[status(thm)],[c_24,c_30]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_488,plain,
% 15.19/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 15.19/2.49      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 15.19/2.49      | sK0 != k1_xboole_0 ),
% 15.19/2.49      inference(unflattening,[status(thm)],[c_487]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1238,plain,
% 15.19/2.49      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 15.19/2.49      | sK0 != k1_xboole_0
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1256,plain,
% 15.19/2.49      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 15.19/2.49      | sK0 != k1_xboole_0
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.19/2.49      inference(demodulation,[status(thm)],[c_1238,c_4]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17979,plain,
% 15.19/2.49      ( k1_relat_1(sK3) = k1_xboole_0
% 15.19/2.49      | sK0 != k1_xboole_0
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.19/2.49      inference(demodulation,[status(thm)],[c_17976,c_1256]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17980,plain,
% 15.19/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 15.19/2.49      | k1_relat_1(sK3) = k1_xboole_0
% 15.19/2.49      | sK0 != k1_xboole_0 ),
% 15.19/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_17979]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17983,plain,
% 15.19/2.49      ( sK2 = k1_xboole_0 ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_17927,c_34,c_95,c_96,c_98,c_1298,c_1316,c_1393,c_1866,
% 15.19/2.49                 c_2063,c_2750,c_4515,c_5052,c_17922,c_17980]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17997,plain,
% 15.19/2.49      ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) = iProver_top ),
% 15.19/2.49      inference(demodulation,[status(thm)],[c_17983,c_2750]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_4820,plain,
% 15.19/2.49      ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_4407,c_34,c_1393]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_4821,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 15.19/2.49      inference(renaming,[status(thm)],[c_4820]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_18054,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_17997,c_4821]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_18721,plain,
% 15.19/2.49      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_18054,c_2064]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1254,plain,
% 15.19/2.49      ( r1_tarski(X0,X0) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2062,plain,
% 15.19/2.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 15.19/2.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1253,c_1243]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_6000,plain,
% 15.19/2.49      ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) = iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1254,c_2062]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_6439,plain,
% 15.19/2.49      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_3,c_6000]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1255,plain,
% 15.19/2.49      ( X0 = X1
% 15.19/2.49      | r1_tarski(X0,X1) != iProver_top
% 15.19/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_6724,plain,
% 15.19/2.49      ( k1_relat_1(k1_xboole_0) = X0
% 15.19/2.49      | r1_tarski(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_6439,c_1255]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_19041,plain,
% 15.19/2.49      ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0) ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_18721,c_6724]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_21172,plain,
% 15.19/2.49      ( k1_relat_1(k1_xboole_0) = sK0 | sK1 = k1_xboole_0 ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_19041,c_3975]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_524,plain,
% 15.19/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 15.19/2.49      | sK1 != sK2
% 15.19/2.49      | sK0 != sK0
% 15.19/2.49      | sK3 != sK3 ),
% 15.19/2.49      inference(resolution_lifted,[status(thm)],[c_166,c_30]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_525,plain,
% 15.19/2.49      ( sK1 != sK2
% 15.19/2.49      | sK0 != sK0
% 15.19/2.49      | sK3 != sK3
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1308,plain,
% 15.19/2.49      ( sK1 != X0 | sK1 = sK2 | sK2 != X0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_762]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1309,plain,
% 15.19/2.49      ( sK1 = sK2 | sK1 != k1_xboole_0 | sK2 != k1_xboole_0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1308]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_21252,plain,
% 15.19/2.49      ( k1_relat_1(k1_xboole_0) = sK0 ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_21172,c_34,c_95,c_96,c_98,c_525,c_1298,c_1309,c_1316,
% 15.19/2.49                 c_1393,c_1482,c_1485,c_1866,c_2063,c_2750,c_4515,c_5052,
% 15.19/2.49                 c_17922,c_17927,c_17980]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_21272,plain,
% 15.19/2.49      ( r1_tarski(sK0,X0) = iProver_top ),
% 15.19/2.49      inference(demodulation,[status(thm)],[c_21252,c_6439]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2057,plain,
% 15.19/2.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1253,c_1242]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_5164,plain,
% 15.19/2.49      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1254,c_2057]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_5305,plain,
% 15.19/2.49      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
% 15.19/2.49      | r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_5164,c_1255]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_21672,plain,
% 15.19/2.49      ( k2_relat_1(k2_zfmisc_1(X0,sK0)) = sK0 ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_21272,c_5305]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1252,plain,
% 15.19/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.19/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_3366,plain,
% 15.19/2.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 15.19/2.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 15.19/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1247,c_1252]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_8882,plain,
% 15.19/2.49      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 15.19/2.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 15.19/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_3,c_3366]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_4405,plain,
% 15.19/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 15.19/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1254,c_3364]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_8894,plain,
% 15.19/2.49      ( r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 15.19/2.49      | r1_tarski(X0,k1_xboole_0) = iProver_top
% 15.19/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_8882,c_2064,c_4405]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_8895,plain,
% 15.19/2.49      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 15.19/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.19/2.49      inference(renaming,[status(thm)],[c_8894]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_22490,plain,
% 15.19/2.49      ( r1_tarski(k2_zfmisc_1(X0,sK0),k1_xboole_0) = iProver_top
% 15.19/2.49      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 15.19/2.49      | v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_21672,c_8895]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_64020,plain,
% 15.19/2.49      ( r1_tarski(k2_zfmisc_1(X0,sK0),k1_xboole_0) = iProver_top
% 15.19/2.49      | v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_22490,c_34,c_95,c_96,c_98,c_525,c_1298,c_1309,c_1316,
% 15.19/2.49                 c_1393,c_1482,c_1485,c_1850,c_1866,c_1981,c_2063,c_2750,
% 15.19/2.49                 c_3889,c_3981,c_4407,c_4515,c_5052,c_6128,c_10827,c_17922,
% 15.19/2.49                 c_17927,c_17980]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_8884,plain,
% 15.19/2.49      ( k2_zfmisc_1(X0,X1) = X2
% 15.19/2.49      | r1_tarski(k2_zfmisc_1(X0,X1),X2) != iProver_top
% 15.19/2.49      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 15.19/2.49      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 15.19/2.49      | v1_relat_1(X2) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_3366,c_1255]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_64106,plain,
% 15.19/2.49      ( k2_zfmisc_1(X0,sK0) = k1_xboole_0
% 15.19/2.49      | r1_tarski(k2_relat_1(k1_xboole_0),sK0) != iProver_top
% 15.19/2.49      | r1_tarski(k1_relat_1(k1_xboole_0),X0) != iProver_top
% 15.19/2.49      | v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top
% 15.19/2.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_64020,c_8884]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_5304,plain,
% 15.19/2.49      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_4,c_5164]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_5333,plain,
% 15.19/2.49      ( k2_relat_1(k1_xboole_0) = X0
% 15.19/2.49      | r1_tarski(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_5304,c_1255]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_9797,plain,
% 15.19/2.49      ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_6439,c_5333]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_21266,plain,
% 15.19/2.49      ( k2_relat_1(k1_xboole_0) = sK0 ),
% 15.19/2.49      inference(demodulation,[status(thm)],[c_21252,c_9797]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_64107,plain,
% 15.19/2.49      ( k2_zfmisc_1(X0,sK0) = k1_xboole_0
% 15.19/2.49      | r1_tarski(sK0,X0) != iProver_top
% 15.19/2.49      | r1_tarski(sK0,sK0) != iProver_top
% 15.19/2.49      | v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top
% 15.19/2.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 15.19/2.49      inference(light_normalisation,[status(thm)],[c_64106,c_21252,c_21266]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_73,plain,
% 15.19/2.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_75,plain,
% 15.19/2.49      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_73]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_97,plain,
% 15.19/2.49      ( r1_tarski(X0,X0) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_99,plain,
% 15.19/2.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_97]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_8,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 15.19/2.49      inference(cnf_transformation,[],[f47]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_229,plain,
% 15.19/2.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.19/2.49      inference(prop_impl,[status(thm)],[c_6]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_230,plain,
% 15.19/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.19/2.49      inference(renaming,[status(thm)],[c_229]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_285,plain,
% 15.19/2.49      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 15.19/2.49      inference(bin_hyper_res,[status(thm)],[c_8,c_230]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1651,plain,
% 15.19/2.49      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 15.19/2.49      | v1_relat_1(X0)
% 15.19/2.49      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_285]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1652,plain,
% 15.19/2.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 15.19/2.49      | v1_relat_1(X0) = iProver_top
% 15.19/2.49      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_1651]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1654,plain,
% 15.19/2.49      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 15.19/2.49      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 15.19/2.49      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1652]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1676,plain,
% 15.19/2.49      ( ~ r1_tarski(X0,X1)
% 15.19/2.49      | r1_tarski(X2,k2_zfmisc_1(X3,X4))
% 15.19/2.49      | X2 != X0
% 15.19/2.49      | k2_zfmisc_1(X3,X4) != X1 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_763]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1677,plain,
% 15.19/2.49      ( X0 != X1
% 15.19/2.49      | k2_zfmisc_1(X2,X3) != X4
% 15.19/2.49      | r1_tarski(X1,X4) != iProver_top
% 15.19/2.49      | r1_tarski(X0,k2_zfmisc_1(X2,X3)) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_1676]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1679,plain,
% 15.19/2.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 15.19/2.49      | k1_xboole_0 != k1_xboole_0
% 15.19/2.49      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 15.19/2.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1677]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_8621,plain,
% 15.19/2.49      ( r1_tarski(sK0,sK0) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_2]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_8622,plain,
% 15.19/2.49      ( r1_tarski(sK0,sK0) = iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_8621]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_64334,plain,
% 15.19/2.49      ( v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top
% 15.19/2.49      | k2_zfmisc_1(X0,sK0) = k1_xboole_0 ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_64107,c_34,c_75,c_95,c_96,c_98,c_99,c_525,c_1298,c_1309,
% 15.19/2.49                 c_1316,c_1393,c_1482,c_1485,c_1654,c_1679,c_1850,c_1866,
% 15.19/2.49                 c_1981,c_2063,c_2750,c_3889,c_3977,c_4407,c_4515,c_5052,
% 15.19/2.49                 c_6128,c_8622,c_10827,c_17922,c_17927,c_17980]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_64335,plain,
% 15.19/2.49      ( k2_zfmisc_1(X0,sK0) = k1_xboole_0
% 15.19/2.49      | v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top ),
% 15.19/2.49      inference(renaming,[status(thm)],[c_64334]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_64338,plain,
% 15.19/2.49      ( k2_zfmisc_1(X0,sK0) = k1_xboole_0 ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_1251,c_64335]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_64389,plain,
% 15.19/2.49      ( sK0 = k1_xboole_0 | k1_xboole_0 = X0 ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_64338,c_5]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1810,plain,
% 15.19/2.49      ( k2_zfmisc_1(X0,sK0) != k1_xboole_0
% 15.19/2.49      | k1_xboole_0 = X0
% 15.19/2.49      | k1_xboole_0 = sK0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_5]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_22,plain,
% 15.19/2.49      ( v1_funct_2(X0,k1_xboole_0,X1)
% 15.19/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 15.19/2.49      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 15.19/2.49      inference(cnf_transformation,[],[f78]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_471,plain,
% 15.19/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 15.19/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 15.19/2.49      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 15.19/2.49      | sK2 != X1
% 15.19/2.49      | sK0 != k1_xboole_0
% 15.19/2.49      | sK3 != X0 ),
% 15.19/2.49      inference(resolution_lifted,[status(thm)],[c_22,c_166]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_472,plain,
% 15.19/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 15.19/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 15.19/2.49      | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 15.19/2.49      | sK0 != k1_xboole_0 ),
% 15.19/2.49      inference(unflattening,[status(thm)],[c_471]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1239,plain,
% 15.19/2.49      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 15.19/2.49      | sK0 != k1_xboole_0
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_472]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1258,plain,
% 15.19/2.49      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 15.19/2.49      | sK0 != k1_xboole_0
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.19/2.49      inference(demodulation,[status(thm)],[c_1239,c_4]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17999,plain,
% 15.19/2.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) != k1_xboole_0
% 15.19/2.49      | sK0 != k1_xboole_0
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.19/2.49      inference(demodulation,[status(thm)],[c_17983,c_1258]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_18002,plain,
% 15.19/2.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) != k1_xboole_0
% 15.19/2.49      | sK0 != k1_xboole_0
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.19/2.49      inference(demodulation,[status(thm)],[c_17999,c_3]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1849,plain,
% 15.19/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 15.19/2.49      | r1_tarski(sK3,k1_xboole_0) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_1847]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_2751,plain,
% 15.19/2.49      ( r1_tarski(k2_relat_1(sK3),sK2) ),
% 15.19/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_2750]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_4822,plain,
% 15.19/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 15.19/2.49      | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
% 15.19/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_4821]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_4259,plain,
% 15.19/2.49      ( k1_relset_1(k1_xboole_0,sK2,sK3) != X0
% 15.19/2.49      | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 15.19/2.49      | k1_xboole_0 != X0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_762]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_7847,plain,
% 15.19/2.49      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_relat_1(sK3)
% 15.19/2.49      | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 15.19/2.49      | k1_xboole_0 != k1_relat_1(sK3) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_4259]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_10826,plain,
% 15.19/2.49      ( ~ r1_tarski(k2_relat_1(sK3),sK2)
% 15.19/2.49      | r1_tarski(k2_relat_1(sK3),k1_xboole_0)
% 15.19/2.49      | k2_relat_1(sK3) != k2_relat_1(sK3)
% 15.19/2.49      | k1_xboole_0 != sK2 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_10824]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_15349,plain,
% 15.19/2.49      ( k1_relat_1(sK3) != X0
% 15.19/2.49      | k1_xboole_0 != X0
% 15.19/2.49      | k1_xboole_0 = k1_relat_1(sK3) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_762]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_15350,plain,
% 15.19/2.49      ( k1_relat_1(sK3) != k1_xboole_0
% 15.19/2.49      | k1_xboole_0 = k1_relat_1(sK3)
% 15.19/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_15349]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17824,plain,
% 15.19/2.49      ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
% 15.19/2.49      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 15.19/2.49      inference(superposition,[status(thm)],[c_2569,c_17818]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17829,plain,
% 15.19/2.49      ( ~ r1_tarski(sK3,k1_xboole_0)
% 15.19/2.49      | k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3) ),
% 15.19/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_17824]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_17831,plain,
% 15.19/2.49      ( ~ r1_tarski(sK3,k1_xboole_0)
% 15.19/2.49      | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_relat_1(sK3) ),
% 15.19/2.49      inference(instantiation,[status(thm)],[c_17829]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_18330,plain,
% 15.19/2.49      ( sK0 != k1_xboole_0 ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_18002,c_34,c_95,c_96,c_98,c_1258,c_1298,c_1316,c_1393,
% 15.19/2.49                 c_1849,c_1866,c_1981,c_2063,c_2750,c_2751,c_3889,c_4407,
% 15.19/2.49                 c_4515,c_4822,c_5052,c_6128,c_7847,c_10826,c_10827,c_15350,
% 15.19/2.49                 c_17831,c_17922,c_17927,c_17979,c_17980]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_65006,plain,
% 15.19/2.49      ( k1_xboole_0 = X0 ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_64389,c_34,c_95,c_96,c_98,c_1258,c_1298,c_1316,c_1352,
% 15.19/2.49                 c_1393,c_1482,c_1810,c_1849,c_1866,c_1981,c_2063,c_2750,
% 15.19/2.49                 c_2751,c_3889,c_4407,c_4515,c_4822,c_5052,c_6128,c_7847,
% 15.19/2.49                 c_10826,c_10827,c_15350,c_17831,c_17922,c_17927,c_17979,
% 15.19/2.49                 c_17980,c_64338]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_590,plain,
% 15.19/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | sK1 != sK2 ),
% 15.19/2.49      inference(equality_resolution_simp,[status(thm)],[c_524]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_1236,plain,
% 15.19/2.49      ( sK1 != sK2
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 15.19/2.49      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_18000,plain,
% 15.19/2.49      ( sK1 != k1_xboole_0
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 15.19/2.49      inference(demodulation,[status(thm)],[c_17983,c_1236]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_18001,plain,
% 15.19/2.49      ( sK1 != k1_xboole_0
% 15.19/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.19/2.49      inference(demodulation,[status(thm)],[c_18000,c_3]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_18296,plain,
% 15.19/2.49      ( sK1 != k1_xboole_0 ),
% 15.19/2.49      inference(global_propositional_subsumption,
% 15.19/2.49                [status(thm)],
% 15.19/2.49                [c_18001,c_34,c_95,c_96,c_98,c_525,c_1298,c_1309,c_1316,
% 15.19/2.49                 c_1393,c_1482,c_1485,c_1866,c_2063,c_2750,c_4515,c_5052,
% 15.19/2.49                 c_17922,c_17927,c_17980]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_65259,plain,
% 15.19/2.49      ( k1_xboole_0 != k1_xboole_0 ),
% 15.19/2.49      inference(demodulation,[status(thm)],[c_65006,c_18296]) ).
% 15.19/2.49  
% 15.19/2.49  cnf(c_65276,plain,
% 15.19/2.49      ( $false ),
% 15.19/2.49      inference(equality_resolution_simp,[status(thm)],[c_65259]) ).
% 15.19/2.49  
% 15.19/2.49  
% 15.19/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.19/2.49  
% 15.19/2.49  ------                               Statistics
% 15.19/2.49  
% 15.19/2.49  ------ General
% 15.19/2.49  
% 15.19/2.49  abstr_ref_over_cycles:                  0
% 15.19/2.49  abstr_ref_under_cycles:                 0
% 15.19/2.49  gc_basic_clause_elim:                   0
% 15.19/2.49  forced_gc_time:                         0
% 15.19/2.49  parsing_time:                           0.009
% 15.19/2.49  unif_index_cands_time:                  0.
% 15.19/2.49  unif_index_add_time:                    0.
% 15.19/2.49  orderings_time:                         0.
% 15.19/2.49  out_proof_time:                         0.03
% 15.19/2.49  total_time:                             1.714
% 15.19/2.49  num_of_symbols:                         49
% 15.19/2.49  num_of_terms:                           61880
% 15.19/2.49  
% 15.19/2.49  ------ Preprocessing
% 15.19/2.49  
% 15.19/2.49  num_of_splits:                          0
% 15.19/2.49  num_of_split_atoms:                     0
% 15.19/2.49  num_of_reused_defs:                     0
% 15.19/2.49  num_eq_ax_congr_red:                    12
% 15.19/2.49  num_of_sem_filtered_clauses:            2
% 15.19/2.49  num_of_subtypes:                        0
% 15.19/2.49  monotx_restored_types:                  0
% 15.19/2.49  sat_num_of_epr_types:                   0
% 15.19/2.49  sat_num_of_non_cyclic_types:            0
% 15.19/2.49  sat_guarded_non_collapsed_types:        0
% 15.19/2.49  num_pure_diseq_elim:                    0
% 15.19/2.49  simp_replaced_by:                       0
% 15.19/2.49  res_preprocessed:                       125
% 15.19/2.49  prep_upred:                             0
% 15.19/2.49  prep_unflattend:                        33
% 15.19/2.49  smt_new_axioms:                         0
% 15.19/2.49  pred_elim_cands:                        3
% 15.19/2.49  pred_elim:                              3
% 15.19/2.49  pred_elim_cl:                           5
% 15.19/2.49  pred_elim_cycles:                       5
% 15.19/2.49  merged_defs:                            8
% 15.19/2.49  merged_defs_ncl:                        0
% 15.19/2.49  bin_hyper_res:                          9
% 15.19/2.49  prep_cycles:                            4
% 15.19/2.49  pred_elim_time:                         0.018
% 15.19/2.49  splitting_time:                         0.
% 15.19/2.49  sem_filter_time:                        0.
% 15.19/2.49  monotx_time:                            0.001
% 15.19/2.49  subtype_inf_time:                       0.
% 15.19/2.49  
% 15.19/2.49  ------ Problem properties
% 15.19/2.49  
% 15.19/2.49  clauses:                                25
% 15.19/2.49  conjectures:                            3
% 15.19/2.49  epr:                                    4
% 15.19/2.49  horn:                                   22
% 15.19/2.49  ground:                                 10
% 15.19/2.49  unary:                                  6
% 15.19/2.49  binary:                                 10
% 15.19/2.49  lits:                                   58
% 15.19/2.49  lits_eq:                                25
% 15.19/2.49  fd_pure:                                0
% 15.19/2.49  fd_pseudo:                              0
% 15.19/2.49  fd_cond:                                1
% 15.19/2.49  fd_pseudo_cond:                         1
% 15.19/2.49  ac_symbols:                             0
% 15.19/2.49  
% 15.19/2.49  ------ Propositional Solver
% 15.19/2.49  
% 15.19/2.49  prop_solver_calls:                      34
% 15.19/2.49  prop_fast_solver_calls:                 3140
% 15.19/2.49  smt_solver_calls:                       0
% 15.19/2.49  smt_fast_solver_calls:                  0
% 15.19/2.49  prop_num_of_clauses:                    27390
% 15.19/2.49  prop_preprocess_simplified:             34783
% 15.19/2.49  prop_fo_subsumed:                       581
% 15.19/2.49  prop_solver_time:                       0.
% 15.19/2.49  smt_solver_time:                        0.
% 15.19/2.49  smt_fast_solver_time:                   0.
% 15.19/2.49  prop_fast_solver_time:                  0.
% 15.19/2.49  prop_unsat_core_time:                   0.
% 15.19/2.49  
% 15.19/2.49  ------ QBF
% 15.19/2.49  
% 15.19/2.49  qbf_q_res:                              0
% 15.19/2.49  qbf_num_tautologies:                    0
% 15.19/2.49  qbf_prep_cycles:                        0
% 15.19/2.49  
% 15.19/2.49  ------ BMC1
% 15.19/2.49  
% 15.19/2.49  bmc1_current_bound:                     -1
% 15.19/2.49  bmc1_last_solved_bound:                 -1
% 15.19/2.49  bmc1_unsat_core_size:                   -1
% 15.19/2.49  bmc1_unsat_core_parents_size:           -1
% 15.19/2.49  bmc1_merge_next_fun:                    0
% 15.19/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.19/2.49  
% 15.19/2.49  ------ Instantiation
% 15.19/2.49  
% 15.19/2.49  inst_num_of_clauses:                    5160
% 15.19/2.49  inst_num_in_passive:                    1461
% 15.19/2.49  inst_num_in_active:                     1985
% 15.19/2.49  inst_num_in_unprocessed:                1714
% 15.19/2.49  inst_num_of_loops:                      2510
% 15.19/2.49  inst_num_of_learning_restarts:          0
% 15.19/2.49  inst_num_moves_active_passive:          520
% 15.19/2.49  inst_lit_activity:                      0
% 15.19/2.49  inst_lit_activity_moves:                0
% 15.19/2.49  inst_num_tautologies:                   0
% 15.19/2.49  inst_num_prop_implied:                  0
% 15.19/2.49  inst_num_existing_simplified:           0
% 15.19/2.49  inst_num_eq_res_simplified:             0
% 15.19/2.49  inst_num_child_elim:                    0
% 15.19/2.49  inst_num_of_dismatching_blockings:      5776
% 15.19/2.49  inst_num_of_non_proper_insts:           8144
% 15.19/2.49  inst_num_of_duplicates:                 0
% 15.19/2.49  inst_inst_num_from_inst_to_res:         0
% 15.19/2.49  inst_dismatching_checking_time:         0.
% 15.19/2.49  
% 15.19/2.49  ------ Resolution
% 15.19/2.49  
% 15.19/2.49  res_num_of_clauses:                     0
% 15.19/2.49  res_num_in_passive:                     0
% 15.19/2.49  res_num_in_active:                      0
% 15.19/2.49  res_num_of_loops:                       129
% 15.19/2.49  res_forward_subset_subsumed:            505
% 15.19/2.49  res_backward_subset_subsumed:           0
% 15.19/2.49  res_forward_subsumed:                   0
% 15.19/2.49  res_backward_subsumed:                  0
% 15.19/2.49  res_forward_subsumption_resolution:     0
% 15.19/2.49  res_backward_subsumption_resolution:    0
% 15.19/2.49  res_clause_to_clause_subsumption:       15604
% 15.19/2.49  res_orphan_elimination:                 0
% 15.19/2.49  res_tautology_del:                      609
% 15.19/2.49  res_num_eq_res_simplified:              1
% 15.19/2.49  res_num_sel_changes:                    0
% 15.19/2.49  res_moves_from_active_to_pass:          0
% 15.19/2.49  
% 15.19/2.49  ------ Superposition
% 15.19/2.49  
% 15.19/2.49  sup_time_total:                         0.
% 15.19/2.49  sup_time_generating:                    0.
% 15.19/2.49  sup_time_sim_full:                      0.
% 15.19/2.49  sup_time_sim_immed:                     0.
% 15.19/2.49  
% 15.19/2.49  sup_num_of_clauses:                     2907
% 15.19/2.49  sup_num_in_active:                      8
% 15.19/2.49  sup_num_in_passive:                     2899
% 15.19/2.49  sup_num_of_loops:                       500
% 15.19/2.49  sup_fw_superposition:                   4784
% 15.19/2.49  sup_bw_superposition:                   3942
% 15.19/2.49  sup_immediate_simplified:               3022
% 15.19/2.49  sup_given_eliminated:                   7
% 15.19/2.49  comparisons_done:                       0
% 15.19/2.49  comparisons_avoided:                    69
% 15.19/2.49  
% 15.19/2.49  ------ Simplifications
% 15.19/2.49  
% 15.19/2.49  
% 15.19/2.49  sim_fw_subset_subsumed:                 165
% 15.19/2.49  sim_bw_subset_subsumed:                 78
% 15.19/2.49  sim_fw_subsumed:                        352
% 15.19/2.49  sim_bw_subsumed:                        111
% 15.19/2.49  sim_fw_subsumption_res:                 0
% 15.19/2.49  sim_bw_subsumption_res:                 0
% 15.19/2.49  sim_tautology_del:                      25
% 15.19/2.49  sim_eq_tautology_del:                   1520
% 15.19/2.49  sim_eq_res_simp:                        1
% 15.19/2.49  sim_fw_demodulated:                     1314
% 15.19/2.49  sim_bw_demodulated:                     455
% 15.19/2.49  sim_light_normalised:                   2009
% 15.19/2.49  sim_joinable_taut:                      0
% 15.19/2.49  sim_joinable_simp:                      0
% 15.19/2.49  sim_ac_normalised:                      0
% 15.19/2.49  sim_smt_subsumption:                    0
% 15.19/2.49  
%------------------------------------------------------------------------------
