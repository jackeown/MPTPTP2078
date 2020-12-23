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
% DateTime   : Thu Dec  3 12:02:40 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :  186 (7495 expanded)
%              Number of clauses        :  119 (2248 expanded)
%              Number of leaves         :   15 (1480 expanded)
%              Depth                    :   28
%              Number of atoms          :  566 (41291 expanded)
%              Number of equality atoms :  300 (8261 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

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
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f53,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
        | ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
        | ~ v1_funct_1(k2_funct_1(sK5)) )
      & k2_relset_1(sK3,sK4,sK5) = sK4
      & v2_funct_1(sK5)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
      | ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
      | ~ v1_funct_1(k2_funct_1(sK5)) )
    & k2_relset_1(sK3,sK4,sK5) = sK4
    & v2_funct_1(sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f53])).

fof(f92,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f93,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f95,plain,(
    k2_relset_1(sK3,sK4,sK5) = sK4 ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f89,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f96,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
    | ~ v1_funct_1(k2_funct_1(sK5)) ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f73,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,(
    v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f72,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f71,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f103,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f67])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f100,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f104,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_730,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X1
    | sK4 != X2
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_40])).

cnf(c_731,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_733,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_731,c_39])).

cnf(c_1691,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1697,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3582,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1691,c_1697])).

cnf(c_3814,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_733,c_3582])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1696,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3106,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1691,c_1696])).

cnf(c_37,negated_conjecture,
    ( k2_relset_1(sK3,sK4,sK5) = sK4 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3122,plain,
    ( k2_relat_1(sK5) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_3106,c_37])).

cnf(c_34,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_36,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
    | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_754,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relat_1(X0) != sK4
    | k2_relat_1(X0) != sK3
    | k2_funct_1(sK5) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_36])).

cnf(c_755,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_relat_1(k2_funct_1(sK5))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relat_1(k2_funct_1(sK5)) != sK4
    | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
    inference(unflattening,[status(thm)],[c_754])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_767,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relat_1(k2_funct_1(sK5)) != sK4
    | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_755,c_19])).

cnf(c_1678,plain,
    ( k1_relat_1(k2_funct_1(sK5)) != sK4
    | k2_relat_1(k2_funct_1(sK5)) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_767])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_38,negated_conjecture,
    ( v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_497,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_38])).

cnf(c_498,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_500,plain,
    ( ~ v1_relat_1(sK5)
    | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_498,c_41])).

cnf(c_1688,plain,
    ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_2026,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2031,plain,
    ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1688,c_41,c_39,c_498,c_2026])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_483,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_38])).

cnf(c_484,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_486,plain,
    ( ~ v1_relat_1(sK5)
    | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_484,c_41])).

cnf(c_1689,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_2035,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1689,c_41,c_39,c_484,c_2026])).

cnf(c_2099,plain,
    ( k1_relat_1(sK5) != sK3
    | k2_relat_1(sK5) != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1678,c_2031,c_2035])).

cnf(c_3188,plain,
    ( k1_relat_1(sK5) != sK3
    | sK4 != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3122,c_2099])).

cnf(c_3192,plain,
    ( k1_relat_1(sK5) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3188])).

cnf(c_42,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_44,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_2027,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2026])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2141,plain,
    ( ~ v1_relat_1(sK5)
    | v1_funct_1(k2_funct_1(sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2142,plain,
    ( v1_relat_1(sK5) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2141])).

cnf(c_4038,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | k1_relat_1(sK5) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3192,c_42,c_44,c_2027,c_2099,c_2142,c_3122])).

cnf(c_4039,plain,
    ( k1_relat_1(sK5) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4038])).

cnf(c_4044,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3814,c_4039])).

cnf(c_33,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1692,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2728,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK5)),k1_relat_1(sK5)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2031,c_1692])).

cnf(c_2739,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK5),k1_relat_1(sK5)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2728,c_2035])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2140,plain,
    ( v1_relat_1(k2_funct_1(sK5))
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2144,plain,
    ( v1_relat_1(k2_funct_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2140])).

cnf(c_2863,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK5),k1_relat_1(sK5)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2739,c_42,c_44,c_2027,c_2142,c_2144])).

cnf(c_3187,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k1_relat_1(sK5)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3122,c_2863])).

cnf(c_3932,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3814,c_3187])).

cnf(c_4047,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4044,c_3932])).

cnf(c_4061,plain,
    ( k2_relat_1(sK5) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4047,c_3122])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k2_relat_1(X2) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_34])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_583,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_567,c_19])).

cnf(c_1686,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1900,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1686,c_10])).

cnf(c_5151,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4061,c_1900])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_124,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2162,plain,
    ( ~ v1_xboole_0(sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2165,plain,
    ( k1_xboole_0 = sK5
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2162])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2171,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2997,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2171])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2998,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_854,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2709,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_4190,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2709])).

cnf(c_4192,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_4190])).

cnf(c_4071,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4047,c_1691])).

cnf(c_4076,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4071,c_10])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1698,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4279,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_1698])).

cnf(c_4842,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4076,c_4279])).

cnf(c_4870,plain,
    ( v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4842])).

cnf(c_5278,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5151,c_124,c_2165,c_2997,c_2998,c_4192,c_4870])).

cnf(c_4057,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK5)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4047,c_3187])).

cnf(c_11,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_4134,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4057,c_11])).

cnf(c_5293,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5278,c_4134])).

cnf(c_3586,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1697])).

cnf(c_5878,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_5293,c_3586])).

cnf(c_3189,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = sK4 ),
    inference(demodulation,[status(thm)],[c_3122,c_2035])).

cnf(c_4060,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4047,c_3189])).

cnf(c_5291,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5278,c_4060])).

cnf(c_5890,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5878,c_5291])).

cnf(c_25,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_647,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK5) != X0
    | sK3 != X1
    | sK4 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_648,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_1683,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_1911,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1683,c_11])).

cnf(c_2308,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | sK4 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1911,c_42,c_44,c_2027,c_2142])).

cnf(c_2309,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2308])).

cnf(c_4065,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4047,c_2309])).

cnf(c_4107,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4065])).

cnf(c_4111,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4107,c_11])).

cnf(c_4138,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4134,c_4111])).

cnf(c_6059,plain,
    ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4138,c_5278])).

cnf(c_6227,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5890,c_6059])).

cnf(c_113,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_112,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6227,c_113,c_112])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:44:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.12/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/0.98  
% 3.12/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.12/0.98  
% 3.12/0.98  ------  iProver source info
% 3.12/0.98  
% 3.12/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.12/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.12/0.98  git: non_committed_changes: false
% 3.12/0.98  git: last_make_outside_of_git: false
% 3.12/0.98  
% 3.12/0.98  ------ 
% 3.12/0.98  
% 3.12/0.98  ------ Input Options
% 3.12/0.98  
% 3.12/0.98  --out_options                           all
% 3.12/0.98  --tptp_safe_out                         true
% 3.12/0.98  --problem_path                          ""
% 3.12/0.98  --include_path                          ""
% 3.12/0.98  --clausifier                            res/vclausify_rel
% 3.12/0.98  --clausifier_options                    --mode clausify
% 3.12/0.98  --stdin                                 false
% 3.12/0.98  --stats_out                             all
% 3.12/0.98  
% 3.12/0.98  ------ General Options
% 3.12/0.98  
% 3.12/0.98  --fof                                   false
% 3.12/0.98  --time_out_real                         305.
% 3.12/0.98  --time_out_virtual                      -1.
% 3.12/0.98  --symbol_type_check                     false
% 3.12/0.98  --clausify_out                          false
% 3.12/0.98  --sig_cnt_out                           false
% 3.12/0.98  --trig_cnt_out                          false
% 3.12/0.98  --trig_cnt_out_tolerance                1.
% 3.12/0.98  --trig_cnt_out_sk_spl                   false
% 3.12/0.98  --abstr_cl_out                          false
% 3.12/0.98  
% 3.12/0.98  ------ Global Options
% 3.12/0.98  
% 3.12/0.98  --schedule                              default
% 3.12/0.98  --add_important_lit                     false
% 3.12/0.98  --prop_solver_per_cl                    1000
% 3.12/0.98  --min_unsat_core                        false
% 3.12/0.98  --soft_assumptions                      false
% 3.12/0.98  --soft_lemma_size                       3
% 3.12/0.98  --prop_impl_unit_size                   0
% 3.12/0.98  --prop_impl_unit                        []
% 3.12/0.98  --share_sel_clauses                     true
% 3.12/0.98  --reset_solvers                         false
% 3.12/0.98  --bc_imp_inh                            [conj_cone]
% 3.12/0.98  --conj_cone_tolerance                   3.
% 3.12/0.98  --extra_neg_conj                        none
% 3.12/0.98  --large_theory_mode                     true
% 3.12/0.98  --prolific_symb_bound                   200
% 3.12/0.98  --lt_threshold                          2000
% 3.12/0.98  --clause_weak_htbl                      true
% 3.12/0.98  --gc_record_bc_elim                     false
% 3.12/0.98  
% 3.12/0.98  ------ Preprocessing Options
% 3.12/0.98  
% 3.12/0.98  --preprocessing_flag                    true
% 3.12/0.98  --time_out_prep_mult                    0.1
% 3.12/0.98  --splitting_mode                        input
% 3.12/0.98  --splitting_grd                         true
% 3.12/0.98  --splitting_cvd                         false
% 3.12/0.98  --splitting_cvd_svl                     false
% 3.12/0.98  --splitting_nvd                         32
% 3.12/0.98  --sub_typing                            true
% 3.12/0.98  --prep_gs_sim                           true
% 3.12/0.98  --prep_unflatten                        true
% 3.12/0.98  --prep_res_sim                          true
% 3.12/0.98  --prep_upred                            true
% 3.12/0.98  --prep_sem_filter                       exhaustive
% 3.12/0.98  --prep_sem_filter_out                   false
% 3.12/0.98  --pred_elim                             true
% 3.12/0.98  --res_sim_input                         true
% 3.12/0.98  --eq_ax_congr_red                       true
% 3.12/0.98  --pure_diseq_elim                       true
% 3.12/0.98  --brand_transform                       false
% 3.12/0.98  --non_eq_to_eq                          false
% 3.12/0.98  --prep_def_merge                        true
% 3.12/0.98  --prep_def_merge_prop_impl              false
% 3.12/0.98  --prep_def_merge_mbd                    true
% 3.12/0.98  --prep_def_merge_tr_red                 false
% 3.12/0.98  --prep_def_merge_tr_cl                  false
% 3.12/0.98  --smt_preprocessing                     true
% 3.12/0.98  --smt_ac_axioms                         fast
% 3.12/0.98  --preprocessed_out                      false
% 3.12/0.98  --preprocessed_stats                    false
% 3.12/0.98  
% 3.12/0.98  ------ Abstraction refinement Options
% 3.12/0.98  
% 3.12/0.98  --abstr_ref                             []
% 3.12/0.98  --abstr_ref_prep                        false
% 3.12/0.98  --abstr_ref_until_sat                   false
% 3.12/0.98  --abstr_ref_sig_restrict                funpre
% 3.12/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/0.98  --abstr_ref_under                       []
% 3.12/0.98  
% 3.12/0.98  ------ SAT Options
% 3.12/0.98  
% 3.12/0.98  --sat_mode                              false
% 3.12/0.98  --sat_fm_restart_options                ""
% 3.12/0.98  --sat_gr_def                            false
% 3.12/0.98  --sat_epr_types                         true
% 3.12/0.98  --sat_non_cyclic_types                  false
% 3.12/0.98  --sat_finite_models                     false
% 3.12/0.98  --sat_fm_lemmas                         false
% 3.12/0.98  --sat_fm_prep                           false
% 3.12/0.98  --sat_fm_uc_incr                        true
% 3.12/0.98  --sat_out_model                         small
% 3.12/0.98  --sat_out_clauses                       false
% 3.12/0.98  
% 3.12/0.98  ------ QBF Options
% 3.12/0.98  
% 3.12/0.98  --qbf_mode                              false
% 3.12/0.98  --qbf_elim_univ                         false
% 3.12/0.98  --qbf_dom_inst                          none
% 3.12/0.98  --qbf_dom_pre_inst                      false
% 3.12/0.98  --qbf_sk_in                             false
% 3.12/0.98  --qbf_pred_elim                         true
% 3.12/0.98  --qbf_split                             512
% 3.12/0.98  
% 3.12/0.98  ------ BMC1 Options
% 3.12/0.98  
% 3.12/0.98  --bmc1_incremental                      false
% 3.12/0.98  --bmc1_axioms                           reachable_all
% 3.12/0.98  --bmc1_min_bound                        0
% 3.12/0.98  --bmc1_max_bound                        -1
% 3.12/0.98  --bmc1_max_bound_default                -1
% 3.12/0.98  --bmc1_symbol_reachability              true
% 3.12/0.98  --bmc1_property_lemmas                  false
% 3.12/0.98  --bmc1_k_induction                      false
% 3.12/0.98  --bmc1_non_equiv_states                 false
% 3.12/0.98  --bmc1_deadlock                         false
% 3.12/0.98  --bmc1_ucm                              false
% 3.12/0.98  --bmc1_add_unsat_core                   none
% 3.12/0.98  --bmc1_unsat_core_children              false
% 3.12/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/0.98  --bmc1_out_stat                         full
% 3.12/0.98  --bmc1_ground_init                      false
% 3.12/0.98  --bmc1_pre_inst_next_state              false
% 3.12/0.98  --bmc1_pre_inst_state                   false
% 3.12/0.98  --bmc1_pre_inst_reach_state             false
% 3.12/0.98  --bmc1_out_unsat_core                   false
% 3.12/0.98  --bmc1_aig_witness_out                  false
% 3.12/0.98  --bmc1_verbose                          false
% 3.12/0.98  --bmc1_dump_clauses_tptp                false
% 3.12/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.12/0.98  --bmc1_dump_file                        -
% 3.12/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.12/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.12/0.98  --bmc1_ucm_extend_mode                  1
% 3.12/0.98  --bmc1_ucm_init_mode                    2
% 3.12/0.98  --bmc1_ucm_cone_mode                    none
% 3.12/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.12/0.98  --bmc1_ucm_relax_model                  4
% 3.12/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.12/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/0.98  --bmc1_ucm_layered_model                none
% 3.12/0.98  --bmc1_ucm_max_lemma_size               10
% 3.12/0.98  
% 3.12/0.98  ------ AIG Options
% 3.12/0.98  
% 3.12/0.98  --aig_mode                              false
% 3.12/0.98  
% 3.12/0.98  ------ Instantiation Options
% 3.12/0.98  
% 3.12/0.98  --instantiation_flag                    true
% 3.12/0.98  --inst_sos_flag                         false
% 3.12/0.98  --inst_sos_phase                        true
% 3.12/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/0.98  --inst_lit_sel_side                     num_symb
% 3.12/0.98  --inst_solver_per_active                1400
% 3.12/0.98  --inst_solver_calls_frac                1.
% 3.12/0.98  --inst_passive_queue_type               priority_queues
% 3.12/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/0.98  --inst_passive_queues_freq              [25;2]
% 3.12/0.98  --inst_dismatching                      true
% 3.12/0.98  --inst_eager_unprocessed_to_passive     true
% 3.12/0.98  --inst_prop_sim_given                   true
% 3.12/0.98  --inst_prop_sim_new                     false
% 3.12/0.98  --inst_subs_new                         false
% 3.12/0.98  --inst_eq_res_simp                      false
% 3.12/0.98  --inst_subs_given                       false
% 3.12/0.98  --inst_orphan_elimination               true
% 3.12/0.98  --inst_learning_loop_flag               true
% 3.12/0.98  --inst_learning_start                   3000
% 3.12/0.98  --inst_learning_factor                  2
% 3.12/0.98  --inst_start_prop_sim_after_learn       3
% 3.12/0.98  --inst_sel_renew                        solver
% 3.12/0.98  --inst_lit_activity_flag                true
% 3.12/0.98  --inst_restr_to_given                   false
% 3.12/0.98  --inst_activity_threshold               500
% 3.12/0.98  --inst_out_proof                        true
% 3.12/0.98  
% 3.12/0.98  ------ Resolution Options
% 3.12/0.98  
% 3.12/0.98  --resolution_flag                       true
% 3.12/0.98  --res_lit_sel                           adaptive
% 3.12/0.98  --res_lit_sel_side                      none
% 3.12/0.98  --res_ordering                          kbo
% 3.12/0.98  --res_to_prop_solver                    active
% 3.12/0.98  --res_prop_simpl_new                    false
% 3.12/0.98  --res_prop_simpl_given                  true
% 3.12/0.98  --res_passive_queue_type                priority_queues
% 3.12/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/0.98  --res_passive_queues_freq               [15;5]
% 3.12/0.98  --res_forward_subs                      full
% 3.12/0.98  --res_backward_subs                     full
% 3.12/0.98  --res_forward_subs_resolution           true
% 3.12/0.98  --res_backward_subs_resolution          true
% 3.12/0.98  --res_orphan_elimination                true
% 3.12/0.98  --res_time_limit                        2.
% 3.12/0.98  --res_out_proof                         true
% 3.12/0.98  
% 3.12/0.98  ------ Superposition Options
% 3.12/0.98  
% 3.12/0.98  --superposition_flag                    true
% 3.12/0.98  --sup_passive_queue_type                priority_queues
% 3.12/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.12/0.98  --demod_completeness_check              fast
% 3.12/0.98  --demod_use_ground                      true
% 3.12/0.98  --sup_to_prop_solver                    passive
% 3.12/0.98  --sup_prop_simpl_new                    true
% 3.12/0.98  --sup_prop_simpl_given                  true
% 3.12/0.98  --sup_fun_splitting                     false
% 3.12/0.98  --sup_smt_interval                      50000
% 3.12/0.98  
% 3.12/0.98  ------ Superposition Simplification Setup
% 3.12/0.98  
% 3.12/0.98  --sup_indices_passive                   []
% 3.12/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.98  --sup_full_bw                           [BwDemod]
% 3.12/0.98  --sup_immed_triv                        [TrivRules]
% 3.12/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.98  --sup_immed_bw_main                     []
% 3.12/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.98  
% 3.12/0.98  ------ Combination Options
% 3.12/0.98  
% 3.12/0.98  --comb_res_mult                         3
% 3.12/0.98  --comb_sup_mult                         2
% 3.12/0.98  --comb_inst_mult                        10
% 3.12/0.98  
% 3.12/0.98  ------ Debug Options
% 3.12/0.98  
% 3.12/0.98  --dbg_backtrace                         false
% 3.12/0.98  --dbg_dump_prop_clauses                 false
% 3.12/0.98  --dbg_dump_prop_clauses_file            -
% 3.12/0.98  --dbg_out_stat                          false
% 3.12/0.98  ------ Parsing...
% 3.12/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.12/0.98  
% 3.12/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.12/0.98  
% 3.12/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.12/0.98  
% 3.12/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.12/0.98  ------ Proving...
% 3.12/0.98  ------ Problem Properties 
% 3.12/0.98  
% 3.12/0.98  
% 3.12/0.98  clauses                                 44
% 3.12/0.98  conjectures                             3
% 3.12/0.98  EPR                                     7
% 3.12/0.98  Horn                                    35
% 3.12/0.98  unary                                   11
% 3.12/0.98  binary                                  15
% 3.12/0.98  lits                                    108
% 3.12/0.98  lits eq                                 43
% 3.12/0.98  fd_pure                                 0
% 3.12/0.98  fd_pseudo                               0
% 3.12/0.98  fd_cond                                 4
% 3.12/0.98  fd_pseudo_cond                          1
% 3.12/0.98  AC symbols                              0
% 3.12/0.98  
% 3.12/0.98  ------ Schedule dynamic 5 is on 
% 3.12/0.98  
% 3.12/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.12/0.98  
% 3.12/0.98  
% 3.12/0.98  ------ 
% 3.12/0.98  Current options:
% 3.12/0.98  ------ 
% 3.12/0.98  
% 3.12/0.98  ------ Input Options
% 3.12/0.98  
% 3.12/0.98  --out_options                           all
% 3.12/0.98  --tptp_safe_out                         true
% 3.12/0.98  --problem_path                          ""
% 3.12/0.98  --include_path                          ""
% 3.12/0.98  --clausifier                            res/vclausify_rel
% 3.12/0.98  --clausifier_options                    --mode clausify
% 3.12/0.98  --stdin                                 false
% 3.12/0.98  --stats_out                             all
% 3.12/0.98  
% 3.12/0.98  ------ General Options
% 3.12/0.98  
% 3.12/0.98  --fof                                   false
% 3.12/0.98  --time_out_real                         305.
% 3.12/0.98  --time_out_virtual                      -1.
% 3.12/0.98  --symbol_type_check                     false
% 3.12/0.98  --clausify_out                          false
% 3.12/0.98  --sig_cnt_out                           false
% 3.12/0.98  --trig_cnt_out                          false
% 3.12/0.98  --trig_cnt_out_tolerance                1.
% 3.12/0.98  --trig_cnt_out_sk_spl                   false
% 3.12/0.98  --abstr_cl_out                          false
% 3.12/0.98  
% 3.12/0.98  ------ Global Options
% 3.12/0.98  
% 3.12/0.98  --schedule                              default
% 3.12/0.98  --add_important_lit                     false
% 3.12/0.98  --prop_solver_per_cl                    1000
% 3.12/0.98  --min_unsat_core                        false
% 3.12/0.98  --soft_assumptions                      false
% 3.12/0.98  --soft_lemma_size                       3
% 3.12/0.98  --prop_impl_unit_size                   0
% 3.12/0.98  --prop_impl_unit                        []
% 3.12/0.98  --share_sel_clauses                     true
% 3.12/0.98  --reset_solvers                         false
% 3.12/0.98  --bc_imp_inh                            [conj_cone]
% 3.12/0.98  --conj_cone_tolerance                   3.
% 3.12/0.98  --extra_neg_conj                        none
% 3.12/0.98  --large_theory_mode                     true
% 3.12/0.98  --prolific_symb_bound                   200
% 3.12/0.98  --lt_threshold                          2000
% 3.12/0.98  --clause_weak_htbl                      true
% 3.12/0.98  --gc_record_bc_elim                     false
% 3.12/0.98  
% 3.12/0.98  ------ Preprocessing Options
% 3.12/0.98  
% 3.12/0.98  --preprocessing_flag                    true
% 3.12/0.98  --time_out_prep_mult                    0.1
% 3.12/0.98  --splitting_mode                        input
% 3.12/0.98  --splitting_grd                         true
% 3.12/0.98  --splitting_cvd                         false
% 3.12/0.98  --splitting_cvd_svl                     false
% 3.12/0.98  --splitting_nvd                         32
% 3.12/0.98  --sub_typing                            true
% 3.12/0.98  --prep_gs_sim                           true
% 3.12/0.98  --prep_unflatten                        true
% 3.12/0.98  --prep_res_sim                          true
% 3.12/0.98  --prep_upred                            true
% 3.12/0.98  --prep_sem_filter                       exhaustive
% 3.12/0.98  --prep_sem_filter_out                   false
% 3.12/0.98  --pred_elim                             true
% 3.12/0.98  --res_sim_input                         true
% 3.12/0.98  --eq_ax_congr_red                       true
% 3.12/0.98  --pure_diseq_elim                       true
% 3.12/0.98  --brand_transform                       false
% 3.12/0.98  --non_eq_to_eq                          false
% 3.12/0.98  --prep_def_merge                        true
% 3.12/0.98  --prep_def_merge_prop_impl              false
% 3.12/0.98  --prep_def_merge_mbd                    true
% 3.12/0.98  --prep_def_merge_tr_red                 false
% 3.12/0.98  --prep_def_merge_tr_cl                  false
% 3.12/0.98  --smt_preprocessing                     true
% 3.12/0.98  --smt_ac_axioms                         fast
% 3.12/0.98  --preprocessed_out                      false
% 3.12/0.98  --preprocessed_stats                    false
% 3.12/0.98  
% 3.12/0.98  ------ Abstraction refinement Options
% 3.12/0.98  
% 3.12/0.98  --abstr_ref                             []
% 3.12/0.98  --abstr_ref_prep                        false
% 3.12/0.98  --abstr_ref_until_sat                   false
% 3.12/0.98  --abstr_ref_sig_restrict                funpre
% 3.12/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/0.98  --abstr_ref_under                       []
% 3.12/0.98  
% 3.12/0.98  ------ SAT Options
% 3.12/0.98  
% 3.12/0.98  --sat_mode                              false
% 3.12/0.98  --sat_fm_restart_options                ""
% 3.12/0.98  --sat_gr_def                            false
% 3.12/0.98  --sat_epr_types                         true
% 3.12/0.98  --sat_non_cyclic_types                  false
% 3.12/0.98  --sat_finite_models                     false
% 3.12/0.98  --sat_fm_lemmas                         false
% 3.12/0.98  --sat_fm_prep                           false
% 3.12/0.98  --sat_fm_uc_incr                        true
% 3.12/0.98  --sat_out_model                         small
% 3.12/0.98  --sat_out_clauses                       false
% 3.12/0.98  
% 3.12/0.98  ------ QBF Options
% 3.12/0.98  
% 3.12/0.98  --qbf_mode                              false
% 3.12/0.98  --qbf_elim_univ                         false
% 3.12/0.98  --qbf_dom_inst                          none
% 3.12/0.98  --qbf_dom_pre_inst                      false
% 3.12/0.98  --qbf_sk_in                             false
% 3.12/0.98  --qbf_pred_elim                         true
% 3.12/0.98  --qbf_split                             512
% 3.12/0.98  
% 3.12/0.98  ------ BMC1 Options
% 3.12/0.98  
% 3.12/0.98  --bmc1_incremental                      false
% 3.12/0.98  --bmc1_axioms                           reachable_all
% 3.12/0.98  --bmc1_min_bound                        0
% 3.12/0.98  --bmc1_max_bound                        -1
% 3.12/0.98  --bmc1_max_bound_default                -1
% 3.12/0.98  --bmc1_symbol_reachability              true
% 3.12/0.98  --bmc1_property_lemmas                  false
% 3.12/0.98  --bmc1_k_induction                      false
% 3.12/0.98  --bmc1_non_equiv_states                 false
% 3.12/0.98  --bmc1_deadlock                         false
% 3.12/0.98  --bmc1_ucm                              false
% 3.12/0.98  --bmc1_add_unsat_core                   none
% 3.12/0.98  --bmc1_unsat_core_children              false
% 3.12/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/0.98  --bmc1_out_stat                         full
% 3.12/0.98  --bmc1_ground_init                      false
% 3.12/0.98  --bmc1_pre_inst_next_state              false
% 3.12/0.98  --bmc1_pre_inst_state                   false
% 3.12/0.98  --bmc1_pre_inst_reach_state             false
% 3.12/0.98  --bmc1_out_unsat_core                   false
% 3.12/0.98  --bmc1_aig_witness_out                  false
% 3.12/0.98  --bmc1_verbose                          false
% 3.12/0.98  --bmc1_dump_clauses_tptp                false
% 3.12/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.12/0.98  --bmc1_dump_file                        -
% 3.12/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.12/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.12/0.98  --bmc1_ucm_extend_mode                  1
% 3.12/0.98  --bmc1_ucm_init_mode                    2
% 3.12/0.98  --bmc1_ucm_cone_mode                    none
% 3.12/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.12/0.98  --bmc1_ucm_relax_model                  4
% 3.12/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.12/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/0.98  --bmc1_ucm_layered_model                none
% 3.12/0.98  --bmc1_ucm_max_lemma_size               10
% 3.12/0.98  
% 3.12/0.98  ------ AIG Options
% 3.12/0.98  
% 3.12/0.98  --aig_mode                              false
% 3.12/0.98  
% 3.12/0.98  ------ Instantiation Options
% 3.12/0.98  
% 3.12/0.98  --instantiation_flag                    true
% 3.12/0.98  --inst_sos_flag                         false
% 3.12/0.98  --inst_sos_phase                        true
% 3.12/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/0.98  --inst_lit_sel_side                     none
% 3.12/0.98  --inst_solver_per_active                1400
% 3.12/0.98  --inst_solver_calls_frac                1.
% 3.12/0.98  --inst_passive_queue_type               priority_queues
% 3.12/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/0.98  --inst_passive_queues_freq              [25;2]
% 3.12/0.98  --inst_dismatching                      true
% 3.12/0.98  --inst_eager_unprocessed_to_passive     true
% 3.12/0.98  --inst_prop_sim_given                   true
% 3.12/0.98  --inst_prop_sim_new                     false
% 3.12/0.98  --inst_subs_new                         false
% 3.12/0.98  --inst_eq_res_simp                      false
% 3.12/0.98  --inst_subs_given                       false
% 3.12/0.98  --inst_orphan_elimination               true
% 3.12/0.98  --inst_learning_loop_flag               true
% 3.12/0.98  --inst_learning_start                   3000
% 3.12/0.98  --inst_learning_factor                  2
% 3.12/0.98  --inst_start_prop_sim_after_learn       3
% 3.12/0.98  --inst_sel_renew                        solver
% 3.12/0.98  --inst_lit_activity_flag                true
% 3.12/0.98  --inst_restr_to_given                   false
% 3.12/0.98  --inst_activity_threshold               500
% 3.12/0.98  --inst_out_proof                        true
% 3.12/0.98  
% 3.12/0.98  ------ Resolution Options
% 3.12/0.98  
% 3.12/0.98  --resolution_flag                       false
% 3.12/0.98  --res_lit_sel                           adaptive
% 3.12/0.98  --res_lit_sel_side                      none
% 3.12/0.98  --res_ordering                          kbo
% 3.12/0.98  --res_to_prop_solver                    active
% 3.12/0.98  --res_prop_simpl_new                    false
% 3.12/0.98  --res_prop_simpl_given                  true
% 3.12/0.98  --res_passive_queue_type                priority_queues
% 3.12/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/0.98  --res_passive_queues_freq               [15;5]
% 3.12/0.98  --res_forward_subs                      full
% 3.12/0.98  --res_backward_subs                     full
% 3.12/0.98  --res_forward_subs_resolution           true
% 3.12/0.98  --res_backward_subs_resolution          true
% 3.12/0.98  --res_orphan_elimination                true
% 3.12/0.98  --res_time_limit                        2.
% 3.12/0.98  --res_out_proof                         true
% 3.12/0.98  
% 3.12/0.98  ------ Superposition Options
% 3.12/0.98  
% 3.12/0.98  --superposition_flag                    true
% 3.12/0.98  --sup_passive_queue_type                priority_queues
% 3.12/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.12/0.98  --demod_completeness_check              fast
% 3.12/0.98  --demod_use_ground                      true
% 3.12/0.98  --sup_to_prop_solver                    passive
% 3.12/0.98  --sup_prop_simpl_new                    true
% 3.12/0.98  --sup_prop_simpl_given                  true
% 3.12/0.98  --sup_fun_splitting                     false
% 3.12/0.98  --sup_smt_interval                      50000
% 3.12/0.98  
% 3.12/0.98  ------ Superposition Simplification Setup
% 3.12/0.98  
% 3.12/0.98  --sup_indices_passive                   []
% 3.12/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.98  --sup_full_bw                           [BwDemod]
% 3.12/0.98  --sup_immed_triv                        [TrivRules]
% 3.12/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.98  --sup_immed_bw_main                     []
% 3.12/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.98  
% 3.12/0.98  ------ Combination Options
% 3.12/0.98  
% 3.12/0.98  --comb_res_mult                         3
% 3.12/0.98  --comb_sup_mult                         2
% 3.12/0.98  --comb_inst_mult                        10
% 3.12/0.98  
% 3.12/0.98  ------ Debug Options
% 3.12/0.98  
% 3.12/0.98  --dbg_backtrace                         false
% 3.12/0.98  --dbg_dump_prop_clauses                 false
% 3.12/0.98  --dbg_dump_prop_clauses_file            -
% 3.12/0.98  --dbg_out_stat                          false
% 3.12/0.98  
% 3.12/0.98  
% 3.12/0.98  
% 3.12/0.98  
% 3.12/0.98  ------ Proving...
% 3.12/0.98  
% 3.12/0.98  
% 3.12/0.98  % SZS status Theorem for theBenchmark.p
% 3.12/0.98  
% 3.12/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.12/0.98  
% 3.12/0.98  fof(f14,axiom,(
% 3.12/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.12/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.98  
% 3.12/0.98  fof(f31,plain,(
% 3.12/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/0.98    inference(ennf_transformation,[],[f14])).
% 3.12/0.98  
% 3.12/0.98  fof(f32,plain,(
% 3.12/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/0.98    inference(flattening,[],[f31])).
% 3.12/0.98  
% 3.12/0.98  fof(f50,plain,(
% 3.12/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/0.98    inference(nnf_transformation,[],[f32])).
% 3.12/0.98  
% 3.12/0.98  fof(f78,plain,(
% 3.12/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/0.98    inference(cnf_transformation,[],[f50])).
% 3.12/0.98  
% 3.12/0.98  fof(f17,conjecture,(
% 3.12/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.12/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.98  
% 3.12/0.98  fof(f18,negated_conjecture,(
% 3.12/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.12/0.98    inference(negated_conjecture,[],[f17])).
% 3.12/0.98  
% 3.12/0.98  fof(f35,plain,(
% 3.12/0.98    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.12/0.98    inference(ennf_transformation,[],[f18])).
% 3.12/0.98  
% 3.12/0.98  fof(f36,plain,(
% 3.12/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.12/0.98    inference(flattening,[],[f35])).
% 3.12/0.98  
% 3.12/0.98  fof(f53,plain,(
% 3.12/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) | ~v1_funct_2(k2_funct_1(sK5),sK4,sK3) | ~v1_funct_1(k2_funct_1(sK5))) & k2_relset_1(sK3,sK4,sK5) = sK4 & v2_funct_1(sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 3.12/0.98    introduced(choice_axiom,[])).
% 3.12/0.98  
% 3.12/0.98  fof(f54,plain,(
% 3.12/0.98    (~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) | ~v1_funct_2(k2_funct_1(sK5),sK4,sK3) | ~v1_funct_1(k2_funct_1(sK5))) & k2_relset_1(sK3,sK4,sK5) = sK4 & v2_funct_1(sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 3.12/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f53])).
% 3.12/0.98  
% 3.12/0.98  fof(f92,plain,(
% 3.12/0.98    v1_funct_2(sK5,sK3,sK4)),
% 3.12/0.98    inference(cnf_transformation,[],[f54])).
% 3.12/0.98  
% 3.12/0.98  fof(f93,plain,(
% 3.12/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.12/0.98    inference(cnf_transformation,[],[f54])).
% 3.12/0.98  
% 3.12/0.98  fof(f12,axiom,(
% 3.12/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.12/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.98  
% 3.12/0.98  fof(f29,plain,(
% 3.12/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/0.98    inference(ennf_transformation,[],[f12])).
% 3.12/0.98  
% 3.12/0.98  fof(f76,plain,(
% 3.12/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/0.98    inference(cnf_transformation,[],[f29])).
% 3.12/0.98  
% 3.12/0.98  fof(f13,axiom,(
% 3.12/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.12/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.98  
% 3.12/0.98  fof(f30,plain,(
% 3.12/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/0.98    inference(ennf_transformation,[],[f13])).
% 3.12/0.98  
% 3.12/0.98  fof(f77,plain,(
% 3.12/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/0.98    inference(cnf_transformation,[],[f30])).
% 3.12/0.98  
% 3.12/0.98  fof(f95,plain,(
% 3.12/0.98    k2_relset_1(sK3,sK4,sK5) = sK4),
% 3.12/0.98    inference(cnf_transformation,[],[f54])).
% 3.12/0.98  
% 3.12/0.98  fof(f16,axiom,(
% 3.12/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.12/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.98  
% 3.12/0.98  fof(f33,plain,(
% 3.12/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.12/0.98    inference(ennf_transformation,[],[f16])).
% 3.12/0.98  
% 3.12/0.98  fof(f34,plain,(
% 3.12/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.12/0.98    inference(flattening,[],[f33])).
% 3.12/0.98  
% 3.12/0.98  fof(f89,plain,(
% 3.12/0.98    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.12/0.98    inference(cnf_transformation,[],[f34])).
% 3.12/0.98  
% 3.12/0.98  fof(f96,plain,(
% 3.12/0.98    ~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) | ~v1_funct_2(k2_funct_1(sK5),sK4,sK3) | ~v1_funct_1(k2_funct_1(sK5))),
% 3.12/0.98    inference(cnf_transformation,[],[f54])).
% 3.12/0.98  
% 3.12/0.98  fof(f10,axiom,(
% 3.12/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.12/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.98  
% 3.12/0.98  fof(f27,plain,(
% 3.12/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/0.98    inference(ennf_transformation,[],[f10])).
% 3.12/0.98  
% 3.12/0.98  fof(f74,plain,(
% 3.12/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/0.98    inference(cnf_transformation,[],[f27])).
% 3.12/0.98  
% 3.12/0.98  fof(f9,axiom,(
% 3.12/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.12/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.98  
% 3.12/0.98  fof(f25,plain,(
% 3.12/0.98    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.12/0.98    inference(ennf_transformation,[],[f9])).
% 3.12/0.98  
% 3.12/0.98  fof(f26,plain,(
% 3.12/0.98    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.12/0.98    inference(flattening,[],[f25])).
% 3.12/0.98  
% 3.12/0.98  fof(f73,plain,(
% 3.12/0.98    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.12/0.98    inference(cnf_transformation,[],[f26])).
% 3.12/0.98  
% 3.12/0.98  fof(f94,plain,(
% 3.12/0.98    v2_funct_1(sK5)),
% 3.12/0.98    inference(cnf_transformation,[],[f54])).
% 3.12/0.98  
% 3.12/0.98  fof(f91,plain,(
% 3.12/0.98    v1_funct_1(sK5)),
% 3.12/0.98    inference(cnf_transformation,[],[f54])).
% 3.12/0.98  
% 3.12/0.98  fof(f72,plain,(
% 3.12/0.98    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.12/0.98    inference(cnf_transformation,[],[f26])).
% 3.12/0.98  
% 3.12/0.98  fof(f8,axiom,(
% 3.12/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.12/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.98  
% 3.12/0.98  fof(f23,plain,(
% 3.12/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.12/0.98    inference(ennf_transformation,[],[f8])).
% 3.12/0.98  
% 3.12/0.98  fof(f24,plain,(
% 3.12/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.12/0.98    inference(flattening,[],[f23])).
% 3.12/0.98  
% 3.12/0.98  fof(f71,plain,(
% 3.12/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.12/0.98    inference(cnf_transformation,[],[f24])).
% 3.12/0.98  
% 3.12/0.98  fof(f90,plain,(
% 3.12/0.98    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.12/0.98    inference(cnf_transformation,[],[f34])).
% 3.12/0.98  
% 3.12/0.98  fof(f70,plain,(
% 3.12/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.12/0.98    inference(cnf_transformation,[],[f24])).
% 3.12/0.98  
% 3.12/0.98  fof(f82,plain,(
% 3.12/0.98    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/0.98    inference(cnf_transformation,[],[f50])).
% 3.12/0.98  
% 3.12/0.98  fof(f103,plain,(
% 3.12/0.98    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.12/0.98    inference(equality_resolution,[],[f82])).
% 3.12/0.98  
% 3.12/0.98  fof(f6,axiom,(
% 3.12/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.12/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.98  
% 3.12/0.98  fof(f47,plain,(
% 3.12/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.12/0.98    inference(nnf_transformation,[],[f6])).
% 3.12/0.98  
% 3.12/0.98  fof(f48,plain,(
% 3.12/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.12/0.98    inference(flattening,[],[f47])).
% 3.12/0.98  
% 3.12/0.98  fof(f67,plain,(
% 3.12/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.12/0.98    inference(cnf_transformation,[],[f48])).
% 3.12/0.98  
% 3.12/0.98  fof(f99,plain,(
% 3.12/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.12/0.98    inference(equality_resolution,[],[f67])).
% 3.12/0.98  
% 3.12/0.98  fof(f3,axiom,(
% 3.12/0.98    v1_xboole_0(k1_xboole_0)),
% 3.12/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.98  
% 3.12/0.98  fof(f60,plain,(
% 3.12/0.98    v1_xboole_0(k1_xboole_0)),
% 3.12/0.98    inference(cnf_transformation,[],[f3])).
% 3.12/0.98  
% 3.12/0.98  fof(f4,axiom,(
% 3.12/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.12/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.98  
% 3.12/0.98  fof(f22,plain,(
% 3.12/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.12/0.98    inference(ennf_transformation,[],[f4])).
% 3.12/0.98  
% 3.12/0.98  fof(f61,plain,(
% 3.12/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.12/0.98    inference(cnf_transformation,[],[f22])).
% 3.12/0.98  
% 3.12/0.98  fof(f5,axiom,(
% 3.12/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.12/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.98  
% 3.12/0.98  fof(f45,plain,(
% 3.12/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.12/0.98    inference(nnf_transformation,[],[f5])).
% 3.12/0.98  
% 3.12/0.98  fof(f46,plain,(
% 3.12/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.12/0.98    inference(flattening,[],[f45])).
% 3.12/0.98  
% 3.12/0.98  fof(f64,plain,(
% 3.12/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.12/0.98    inference(cnf_transformation,[],[f46])).
% 3.12/0.98  
% 3.12/0.98  fof(f62,plain,(
% 3.12/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.12/0.98    inference(cnf_transformation,[],[f46])).
% 3.12/0.98  
% 3.12/0.98  fof(f98,plain,(
% 3.12/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.12/0.98    inference(equality_resolution,[],[f62])).
% 3.12/0.98  
% 3.12/0.98  fof(f11,axiom,(
% 3.12/0.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.12/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/0.98  
% 3.12/0.98  fof(f28,plain,(
% 3.12/0.98    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.12/0.98    inference(ennf_transformation,[],[f11])).
% 3.12/0.98  
% 3.12/0.98  fof(f75,plain,(
% 3.12/0.98    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.12/0.98    inference(cnf_transformation,[],[f28])).
% 3.12/0.98  
% 3.12/0.98  fof(f66,plain,(
% 3.12/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.12/0.98    inference(cnf_transformation,[],[f48])).
% 3.12/0.98  
% 3.12/0.98  fof(f100,plain,(
% 3.12/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.12/0.98    inference(equality_resolution,[],[f66])).
% 3.12/0.98  
% 3.12/0.98  fof(f81,plain,(
% 3.12/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/0.98    inference(cnf_transformation,[],[f50])).
% 3.12/0.98  
% 3.12/0.98  fof(f104,plain,(
% 3.12/0.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.12/0.98    inference(equality_resolution,[],[f81])).
% 3.12/0.98  
% 3.12/0.98  fof(f65,plain,(
% 3.12/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.12/0.98    inference(cnf_transformation,[],[f48])).
% 3.12/0.98  
% 3.12/0.98  cnf(c_28,plain,
% 3.12/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.12/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.12/0.98      | k1_xboole_0 = X2 ),
% 3.12/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_40,negated_conjecture,
% 3.12/0.98      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.12/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_730,plain,
% 3.12/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.12/0.98      | sK3 != X1
% 3.12/0.98      | sK4 != X2
% 3.12/0.98      | sK5 != X0
% 3.12/0.98      | k1_xboole_0 = X2 ),
% 3.12/0.98      inference(resolution_lifted,[status(thm)],[c_28,c_40]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_731,plain,
% 3.12/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.12/0.98      | k1_relset_1(sK3,sK4,sK5) = sK3
% 3.12/0.98      | k1_xboole_0 = sK4 ),
% 3.12/0.98      inference(unflattening,[status(thm)],[c_730]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_39,negated_conjecture,
% 3.12/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.12/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_733,plain,
% 3.12/0.98      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 3.12/0.98      inference(global_propositional_subsumption,
% 3.12/0.98                [status(thm)],
% 3.12/0.98                [c_731,c_39]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_1691,plain,
% 3.12/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.12/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_21,plain,
% 3.12/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.12/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_1697,plain,
% 3.12/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.12/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.12/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_3582,plain,
% 3.12/0.98      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.12/0.98      inference(superposition,[status(thm)],[c_1691,c_1697]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_3814,plain,
% 3.12/0.98      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.12/0.98      inference(superposition,[status(thm)],[c_733,c_3582]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_22,plain,
% 3.12/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.12/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_1696,plain,
% 3.12/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.12/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.12/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_3106,plain,
% 3.12/0.98      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 3.12/0.98      inference(superposition,[status(thm)],[c_1691,c_1696]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_37,negated_conjecture,
% 3.12/0.98      ( k2_relset_1(sK3,sK4,sK5) = sK4 ),
% 3.12/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_3122,plain,
% 3.12/0.98      ( k2_relat_1(sK5) = sK4 ),
% 3.12/0.98      inference(light_normalisation,[status(thm)],[c_3106,c_37]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_34,plain,
% 3.12/0.98      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.12/0.98      | ~ v1_relat_1(X0)
% 3.12/0.98      | ~ v1_funct_1(X0) ),
% 3.12/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_36,negated_conjecture,
% 3.12/0.98      ( ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
% 3.12/0.98      | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.12/0.98      | ~ v1_funct_1(k2_funct_1(sK5)) ),
% 3.12/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_754,plain,
% 3.12/0.98      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.12/0.98      | ~ v1_relat_1(X0)
% 3.12/0.98      | ~ v1_funct_1(X0)
% 3.12/0.98      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.12/0.98      | k1_relat_1(X0) != sK4
% 3.12/0.98      | k2_relat_1(X0) != sK3
% 3.12/0.98      | k2_funct_1(sK5) != X0 ),
% 3.12/0.98      inference(resolution_lifted,[status(thm)],[c_34,c_36]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_755,plain,
% 3.12/0.98      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.12/0.98      | ~ v1_relat_1(k2_funct_1(sK5))
% 3.12/0.98      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.12/0.98      | k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.12/0.98      | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
% 3.12/0.98      inference(unflattening,[status(thm)],[c_754]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_19,plain,
% 3.12/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/0.98      | v1_relat_1(X0) ),
% 3.12/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_767,plain,
% 3.12/0.98      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.12/0.98      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.12/0.98      | k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.12/0.98      | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
% 3.12/0.98      inference(forward_subsumption_resolution,
% 3.12/0.98                [status(thm)],
% 3.12/0.98                [c_755,c_19]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_1678,plain,
% 3.12/0.98      ( k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.12/0.98      | k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.12/0.98      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.12/0.98      inference(predicate_to_equality,[status(thm)],[c_767]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_17,plain,
% 3.12/0.98      ( ~ v2_funct_1(X0)
% 3.12/0.98      | ~ v1_relat_1(X0)
% 3.12/0.98      | ~ v1_funct_1(X0)
% 3.12/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.12/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_38,negated_conjecture,
% 3.12/0.98      ( v2_funct_1(sK5) ),
% 3.12/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_497,plain,
% 3.12/0.98      ( ~ v1_relat_1(X0)
% 3.12/0.98      | ~ v1_funct_1(X0)
% 3.12/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.12/0.98      | sK5 != X0 ),
% 3.12/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_38]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_498,plain,
% 3.12/0.98      ( ~ v1_relat_1(sK5)
% 3.12/0.98      | ~ v1_funct_1(sK5)
% 3.12/0.98      | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
% 3.12/0.98      inference(unflattening,[status(thm)],[c_497]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_41,negated_conjecture,
% 3.12/0.98      ( v1_funct_1(sK5) ),
% 3.12/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_500,plain,
% 3.12/0.98      ( ~ v1_relat_1(sK5)
% 3.12/0.98      | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
% 3.12/0.98      inference(global_propositional_subsumption,
% 3.12/0.98                [status(thm)],
% 3.12/0.98                [c_498,c_41]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_1688,plain,
% 3.12/0.98      ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5)
% 3.12/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.12/0.98      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2026,plain,
% 3.12/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.12/0.98      | v1_relat_1(sK5) ),
% 3.12/0.98      inference(instantiation,[status(thm)],[c_19]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2031,plain,
% 3.12/0.98      ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
% 3.12/0.98      inference(global_propositional_subsumption,
% 3.12/0.98                [status(thm)],
% 3.12/0.98                [c_1688,c_41,c_39,c_498,c_2026]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_18,plain,
% 3.12/0.98      ( ~ v2_funct_1(X0)
% 3.12/0.98      | ~ v1_relat_1(X0)
% 3.12/0.98      | ~ v1_funct_1(X0)
% 3.12/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.12/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_483,plain,
% 3.12/0.98      ( ~ v1_relat_1(X0)
% 3.12/0.98      | ~ v1_funct_1(X0)
% 3.12/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.12/0.98      | sK5 != X0 ),
% 3.12/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_38]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_484,plain,
% 3.12/0.98      ( ~ v1_relat_1(sK5)
% 3.12/0.98      | ~ v1_funct_1(sK5)
% 3.12/0.98      | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
% 3.12/0.98      inference(unflattening,[status(thm)],[c_483]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_486,plain,
% 3.12/0.98      ( ~ v1_relat_1(sK5)
% 3.12/0.98      | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
% 3.12/0.98      inference(global_propositional_subsumption,
% 3.12/0.98                [status(thm)],
% 3.12/0.98                [c_484,c_41]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_1689,plain,
% 3.12/0.98      ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5)
% 3.12/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.12/0.98      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2035,plain,
% 3.12/0.98      ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
% 3.12/0.98      inference(global_propositional_subsumption,
% 3.12/0.98                [status(thm)],
% 3.12/0.98                [c_1689,c_41,c_39,c_484,c_2026]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2099,plain,
% 3.12/0.98      ( k1_relat_1(sK5) != sK3
% 3.12/0.98      | k2_relat_1(sK5) != sK4
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.12/0.98      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.12/0.98      inference(light_normalisation,[status(thm)],[c_1678,c_2031,c_2035]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_3188,plain,
% 3.12/0.98      ( k1_relat_1(sK5) != sK3
% 3.12/0.98      | sK4 != sK4
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.12/0.98      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.12/0.98      inference(demodulation,[status(thm)],[c_3122,c_2099]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_3192,plain,
% 3.12/0.98      ( k1_relat_1(sK5) != sK3
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.12/0.98      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.12/0.98      inference(equality_resolution_simp,[status(thm)],[c_3188]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_42,plain,
% 3.12/0.98      ( v1_funct_1(sK5) = iProver_top ),
% 3.12/0.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_44,plain,
% 3.12/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.12/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2027,plain,
% 3.12/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.12/0.98      | v1_relat_1(sK5) = iProver_top ),
% 3.12/0.98      inference(predicate_to_equality,[status(thm)],[c_2026]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_15,plain,
% 3.12/0.98      ( ~ v1_relat_1(X0)
% 3.12/0.98      | ~ v1_funct_1(X0)
% 3.12/0.98      | v1_funct_1(k2_funct_1(X0)) ),
% 3.12/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2141,plain,
% 3.12/0.98      ( ~ v1_relat_1(sK5)
% 3.12/0.98      | v1_funct_1(k2_funct_1(sK5))
% 3.12/0.98      | ~ v1_funct_1(sK5) ),
% 3.12/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2142,plain,
% 3.12/0.98      ( v1_relat_1(sK5) != iProver_top
% 3.12/0.98      | v1_funct_1(k2_funct_1(sK5)) = iProver_top
% 3.12/0.98      | v1_funct_1(sK5) != iProver_top ),
% 3.12/0.98      inference(predicate_to_equality,[status(thm)],[c_2141]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4038,plain,
% 3.12/0.98      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.12/0.98      | k1_relat_1(sK5) != sK3 ),
% 3.12/0.98      inference(global_propositional_subsumption,
% 3.12/0.98                [status(thm)],
% 3.12/0.98                [c_3192,c_42,c_44,c_2027,c_2099,c_2142,c_3122]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4039,plain,
% 3.12/0.98      ( k1_relat_1(sK5) != sK3
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.12/0.98      inference(renaming,[status(thm)],[c_4038]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4044,plain,
% 3.12/0.98      ( sK4 = k1_xboole_0
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.12/0.98      inference(superposition,[status(thm)],[c_3814,c_4039]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_33,plain,
% 3.12/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.12/0.98      | ~ v1_relat_1(X0)
% 3.12/0.98      | ~ v1_funct_1(X0) ),
% 3.12/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_1692,plain,
% 3.12/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.12/0.98      | v1_relat_1(X0) != iProver_top
% 3.12/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.12/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2728,plain,
% 3.12/0.98      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK5)),k1_relat_1(sK5)))) = iProver_top
% 3.12/0.98      | v1_relat_1(k2_funct_1(sK5)) != iProver_top
% 3.12/0.98      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.12/0.98      inference(superposition,[status(thm)],[c_2031,c_1692]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2739,plain,
% 3.12/0.98      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK5),k1_relat_1(sK5)))) = iProver_top
% 3.12/0.98      | v1_relat_1(k2_funct_1(sK5)) != iProver_top
% 3.12/0.98      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.12/0.98      inference(light_normalisation,[status(thm)],[c_2728,c_2035]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_16,plain,
% 3.12/0.98      ( ~ v1_relat_1(X0)
% 3.12/0.98      | v1_relat_1(k2_funct_1(X0))
% 3.12/0.98      | ~ v1_funct_1(X0) ),
% 3.12/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2140,plain,
% 3.12/0.98      ( v1_relat_1(k2_funct_1(sK5))
% 3.12/0.98      | ~ v1_relat_1(sK5)
% 3.12/0.98      | ~ v1_funct_1(sK5) ),
% 3.12/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2144,plain,
% 3.12/0.98      ( v1_relat_1(k2_funct_1(sK5)) = iProver_top
% 3.12/0.98      | v1_relat_1(sK5) != iProver_top
% 3.12/0.98      | v1_funct_1(sK5) != iProver_top ),
% 3.12/0.98      inference(predicate_to_equality,[status(thm)],[c_2140]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2863,plain,
% 3.12/0.98      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK5),k1_relat_1(sK5)))) = iProver_top ),
% 3.12/0.98      inference(global_propositional_subsumption,
% 3.12/0.98                [status(thm)],
% 3.12/0.98                [c_2739,c_42,c_44,c_2027,c_2142,c_2144]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_3187,plain,
% 3.12/0.98      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k1_relat_1(sK5)))) = iProver_top ),
% 3.12/0.98      inference(demodulation,[status(thm)],[c_3122,c_2863]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_3932,plain,
% 3.12/0.98      ( sK4 = k1_xboole_0
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 3.12/0.98      inference(superposition,[status(thm)],[c_3814,c_3187]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4047,plain,
% 3.12/0.98      ( sK4 = k1_xboole_0 ),
% 3.12/0.98      inference(global_propositional_subsumption,
% 3.12/0.98                [status(thm)],
% 3.12/0.98                [c_4044,c_3932]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4061,plain,
% 3.12/0.98      ( k2_relat_1(sK5) = k1_xboole_0 ),
% 3.12/0.98      inference(demodulation,[status(thm)],[c_4047,c_3122]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_24,plain,
% 3.12/0.98      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.12/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.12/0.98      | k1_xboole_0 = X1
% 3.12/0.98      | k1_xboole_0 = X0 ),
% 3.12/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_566,plain,
% 3.12/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.12/0.98      | ~ v1_relat_1(X2)
% 3.12/0.98      | ~ v1_funct_1(X2)
% 3.12/0.98      | X2 != X0
% 3.12/0.98      | k1_relat_1(X2) != X1
% 3.12/0.98      | k2_relat_1(X2) != k1_xboole_0
% 3.12/0.98      | k1_xboole_0 = X0
% 3.12/0.98      | k1_xboole_0 = X1 ),
% 3.12/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_34]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_567,plain,
% 3.12/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.12/0.98      | ~ v1_relat_1(X0)
% 3.12/0.98      | ~ v1_funct_1(X0)
% 3.12/0.98      | k2_relat_1(X0) != k1_xboole_0
% 3.12/0.98      | k1_xboole_0 = X0
% 3.12/0.98      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.12/0.98      inference(unflattening,[status(thm)],[c_566]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_583,plain,
% 3.12/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.12/0.98      | ~ v1_funct_1(X0)
% 3.12/0.98      | k2_relat_1(X0) != k1_xboole_0
% 3.12/0.98      | k1_xboole_0 = X0
% 3.12/0.98      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.12/0.98      inference(forward_subsumption_resolution,
% 3.12/0.98                [status(thm)],
% 3.12/0.98                [c_567,c_19]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_1686,plain,
% 3.12/0.98      ( k2_relat_1(X0) != k1_xboole_0
% 3.12/0.98      | k1_xboole_0 = X0
% 3.12/0.98      | k1_xboole_0 = k1_relat_1(X0)
% 3.12/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
% 3.12/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.12/0.98      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_10,plain,
% 3.12/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.12/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_1900,plain,
% 3.12/0.98      ( k1_relat_1(X0) = k1_xboole_0
% 3.12/0.98      | k2_relat_1(X0) != k1_xboole_0
% 3.12/0.98      | k1_xboole_0 = X0
% 3.12/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.12/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.12/0.98      inference(demodulation,[status(thm)],[c_1686,c_10]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_5151,plain,
% 3.12/0.98      ( k1_relat_1(sK5) = k1_xboole_0
% 3.12/0.98      | sK5 = k1_xboole_0
% 3.12/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.12/0.98      | v1_funct_1(sK5) != iProver_top ),
% 3.12/0.98      inference(superposition,[status(thm)],[c_4061,c_1900]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_5,plain,
% 3.12/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.12/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_124,plain,
% 3.12/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.12/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_6,plain,
% 3.12/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.12/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2162,plain,
% 3.12/0.98      ( ~ v1_xboole_0(sK5) | k1_xboole_0 = sK5 ),
% 3.12/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2165,plain,
% 3.12/0.98      ( k1_xboole_0 = sK5 | v1_xboole_0(sK5) != iProver_top ),
% 3.12/0.98      inference(predicate_to_equality,[status(thm)],[c_2162]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_7,plain,
% 3.12/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.12/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2171,plain,
% 3.12/0.98      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | X0 = sK5 ),
% 3.12/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2997,plain,
% 3.12/0.98      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 3.12/0.98      inference(instantiation,[status(thm)],[c_2171]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_9,plain,
% 3.12/0.98      ( r1_tarski(X0,X0) ),
% 3.12/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2998,plain,
% 3.12/0.98      ( r1_tarski(sK5,sK5) ),
% 3.12/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_854,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2709,plain,
% 3.12/0.98      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 3.12/0.98      inference(instantiation,[status(thm)],[c_854]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4190,plain,
% 3.12/0.98      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 3.12/0.98      inference(instantiation,[status(thm)],[c_2709]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4192,plain,
% 3.12/0.98      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 3.12/0.98      inference(instantiation,[status(thm)],[c_4190]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4071,plain,
% 3.12/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 3.12/0.98      inference(demodulation,[status(thm)],[c_4047,c_1691]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4076,plain,
% 3.12/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.12/0.98      inference(demodulation,[status(thm)],[c_4071,c_10]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_20,plain,
% 3.12/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/0.98      | ~ v1_xboole_0(X1)
% 3.12/0.98      | v1_xboole_0(X0) ),
% 3.12/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_1698,plain,
% 3.12/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.12/0.98      | v1_xboole_0(X1) != iProver_top
% 3.12/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.12/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4279,plain,
% 3.12/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.12/0.98      | v1_xboole_0(X1) != iProver_top
% 3.12/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.12/0.98      inference(superposition,[status(thm)],[c_10,c_1698]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4842,plain,
% 3.12/0.98      ( v1_xboole_0(X0) != iProver_top | v1_xboole_0(sK5) = iProver_top ),
% 3.12/0.98      inference(superposition,[status(thm)],[c_4076,c_4279]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4870,plain,
% 3.12/0.98      ( v1_xboole_0(sK5) = iProver_top
% 3.12/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.12/0.98      inference(instantiation,[status(thm)],[c_4842]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_5278,plain,
% 3.12/0.98      ( sK5 = k1_xboole_0 ),
% 3.12/0.98      inference(global_propositional_subsumption,
% 3.12/0.98                [status(thm)],
% 3.12/0.98                [c_5151,c_124,c_2165,c_2997,c_2998,c_4192,c_4870]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4057,plain,
% 3.12/0.98      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK5)))) = iProver_top ),
% 3.12/0.98      inference(demodulation,[status(thm)],[c_4047,c_3187]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_11,plain,
% 3.12/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.12/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4134,plain,
% 3.12/0.98      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.12/0.98      inference(demodulation,[status(thm)],[c_4057,c_11]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_5293,plain,
% 3.12/0.98      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.12/0.98      inference(demodulation,[status(thm)],[c_5278,c_4134]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_3586,plain,
% 3.12/0.98      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.12/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.12/0.98      inference(superposition,[status(thm)],[c_11,c_1697]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_5878,plain,
% 3.12/0.98      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
% 3.12/0.98      inference(superposition,[status(thm)],[c_5293,c_3586]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_3189,plain,
% 3.12/0.98      ( k1_relat_1(k2_funct_1(sK5)) = sK4 ),
% 3.12/0.98      inference(demodulation,[status(thm)],[c_3122,c_2035]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4060,plain,
% 3.12/0.98      ( k1_relat_1(k2_funct_1(sK5)) = k1_xboole_0 ),
% 3.12/0.98      inference(demodulation,[status(thm)],[c_4047,c_3189]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_5291,plain,
% 3.12/0.98      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.12/0.98      inference(demodulation,[status(thm)],[c_5278,c_4060]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_5890,plain,
% 3.12/0.98      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.12/0.98      inference(light_normalisation,[status(thm)],[c_5878,c_5291]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_25,plain,
% 3.12/0.98      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.12/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.12/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.12/0.98      inference(cnf_transformation,[],[f104]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_647,plain,
% 3.12/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.12/0.98      | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.12/0.98      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.12/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.12/0.98      | k2_funct_1(sK5) != X0
% 3.12/0.98      | sK3 != X1
% 3.12/0.98      | sK4 != k1_xboole_0 ),
% 3.12/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_36]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_648,plain,
% 3.12/0.98      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.12/0.98      | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
% 3.12/0.98      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.12/0.98      | k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
% 3.12/0.98      | sK4 != k1_xboole_0 ),
% 3.12/0.98      inference(unflattening,[status(thm)],[c_647]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_1683,plain,
% 3.12/0.98      ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
% 3.12/0.98      | sK4 != k1_xboole_0
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 3.12/0.98      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.12/0.98      inference(predicate_to_equality,[status(thm)],[c_648]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_1911,plain,
% 3.12/0.98      ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
% 3.12/0.98      | sK4 != k1_xboole_0
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.12/0.98      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.12/0.98      inference(demodulation,[status(thm)],[c_1683,c_11]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2308,plain,
% 3.12/0.98      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.12/0.98      | sK4 != k1_xboole_0
% 3.12/0.98      | k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0 ),
% 3.12/0.98      inference(global_propositional_subsumption,
% 3.12/0.98                [status(thm)],
% 3.12/0.98                [c_1911,c_42,c_44,c_2027,c_2142]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_2309,plain,
% 3.12/0.98      ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
% 3.12/0.98      | sK4 != k1_xboole_0
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.12/0.98      inference(renaming,[status(thm)],[c_2308]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4065,plain,
% 3.12/0.98      ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
% 3.12/0.98      | k1_xboole_0 != k1_xboole_0
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.12/0.98      inference(demodulation,[status(thm)],[c_4047,c_2309]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4107,plain,
% 3.12/0.98      ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.12/0.98      inference(equality_resolution_simp,[status(thm)],[c_4065]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4111,plain,
% 3.12/0.98      ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0
% 3.12/0.98      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.12/0.98      inference(demodulation,[status(thm)],[c_4107,c_11]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_4138,plain,
% 3.12/0.98      ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(sK5)) != k1_xboole_0 ),
% 3.12/0.98      inference(backward_subsumption_resolution,
% 3.12/0.98                [status(thm)],
% 3.12/0.98                [c_4134,c_4111]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_6059,plain,
% 3.12/0.98      ( k1_relset_1(k1_xboole_0,sK3,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 3.12/0.98      inference(light_normalisation,[status(thm)],[c_4138,c_5278]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_6227,plain,
% 3.12/0.98      ( k1_xboole_0 != k1_xboole_0 ),
% 3.12/0.98      inference(demodulation,[status(thm)],[c_5890,c_6059]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_113,plain,
% 3.12/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.12/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_12,plain,
% 3.12/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.12/0.98      | k1_xboole_0 = X0
% 3.12/0.98      | k1_xboole_0 = X1 ),
% 3.12/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(c_112,plain,
% 3.12/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.12/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.12/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.12/0.98  
% 3.12/0.98  cnf(contradiction,plain,
% 3.12/0.98      ( $false ),
% 3.12/0.98      inference(minisat,[status(thm)],[c_6227,c_113,c_112]) ).
% 3.12/0.98  
% 3.12/0.98  
% 3.12/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.12/0.98  
% 3.12/0.98  ------                               Statistics
% 3.12/0.98  
% 3.12/0.98  ------ General
% 3.12/0.98  
% 3.12/0.98  abstr_ref_over_cycles:                  0
% 3.12/0.98  abstr_ref_under_cycles:                 0
% 3.12/0.98  gc_basic_clause_elim:                   0
% 3.12/0.98  forced_gc_time:                         0
% 3.12/0.98  parsing_time:                           0.009
% 3.12/0.98  unif_index_cands_time:                  0.
% 3.12/0.98  unif_index_add_time:                    0.
% 3.12/0.98  orderings_time:                         0.
% 3.12/0.98  out_proof_time:                         0.01
% 3.12/0.98  total_time:                             0.188
% 3.12/0.98  num_of_symbols:                         53
% 3.12/0.98  num_of_terms:                           4840
% 3.12/0.98  
% 3.12/0.98  ------ Preprocessing
% 3.12/0.98  
% 3.12/0.98  num_of_splits:                          0
% 3.12/0.98  num_of_split_atoms:                     0
% 3.12/0.98  num_of_reused_defs:                     0
% 3.12/0.98  num_eq_ax_congr_red:                    16
% 3.12/0.98  num_of_sem_filtered_clauses:            1
% 3.12/0.98  num_of_subtypes:                        0
% 3.12/0.98  monotx_restored_types:                  0
% 3.12/0.98  sat_num_of_epr_types:                   0
% 3.12/0.98  sat_num_of_non_cyclic_types:            0
% 3.12/0.98  sat_guarded_non_collapsed_types:        0
% 3.12/0.98  num_pure_diseq_elim:                    0
% 3.12/0.98  simp_replaced_by:                       0
% 3.12/0.98  res_preprocessed:                       159
% 3.12/0.98  prep_upred:                             0
% 3.12/0.98  prep_unflattend:                        54
% 3.12/0.98  smt_new_axioms:                         0
% 3.12/0.98  pred_elim_cands:                        8
% 3.12/0.98  pred_elim:                              2
% 3.12/0.98  pred_elim_cl:                           -4
% 3.12/0.98  pred_elim_cycles:                       3
% 3.12/0.98  merged_defs:                            6
% 3.12/0.98  merged_defs_ncl:                        0
% 3.12/0.98  bin_hyper_res:                          6
% 3.12/0.98  prep_cycles:                            3
% 3.12/0.98  pred_elim_time:                         0.009
% 3.12/0.98  splitting_time:                         0.
% 3.12/0.98  sem_filter_time:                        0.
% 3.12/0.98  monotx_time:                            0.
% 3.12/0.98  subtype_inf_time:                       0.
% 3.12/0.98  
% 3.12/0.98  ------ Problem properties
% 3.12/0.98  
% 3.12/0.98  clauses:                                44
% 3.12/0.98  conjectures:                            3
% 3.12/0.98  epr:                                    7
% 3.12/0.98  horn:                                   35
% 3.12/0.98  ground:                                 15
% 3.12/0.98  unary:                                  11
% 3.12/0.98  binary:                                 15
% 3.12/0.98  lits:                                   108
% 3.12/0.98  lits_eq:                                43
% 3.12/0.98  fd_pure:                                0
% 3.12/0.98  fd_pseudo:                              0
% 3.12/0.98  fd_cond:                                4
% 3.12/0.98  fd_pseudo_cond:                         1
% 3.12/0.98  ac_symbols:                             0
% 3.12/0.98  
% 3.12/0.98  ------ Propositional Solver
% 3.12/0.98  
% 3.12/0.98  prop_solver_calls:                      24
% 3.12/0.98  prop_fast_solver_calls:                 1137
% 3.12/0.98  smt_solver_calls:                       0
% 3.12/0.98  smt_fast_solver_calls:                  0
% 3.12/0.98  prop_num_of_clauses:                    2071
% 3.12/0.98  prop_preprocess_simplified:             6679
% 3.12/0.98  prop_fo_subsumed:                       34
% 3.12/0.98  prop_solver_time:                       0.
% 3.12/0.98  smt_solver_time:                        0.
% 3.12/0.98  smt_fast_solver_time:                   0.
% 3.12/0.98  prop_fast_solver_time:                  0.
% 3.12/0.98  prop_unsat_core_time:                   0.
% 3.12/0.98  
% 3.12/0.98  ------ QBF
% 3.12/0.98  
% 3.12/0.98  qbf_q_res:                              0
% 3.12/0.98  qbf_num_tautologies:                    0
% 3.12/0.98  qbf_prep_cycles:                        0
% 3.12/0.98  
% 3.12/0.98  ------ BMC1
% 3.12/0.98  
% 3.12/0.98  bmc1_current_bound:                     -1
% 3.12/0.98  bmc1_last_solved_bound:                 -1
% 3.12/0.98  bmc1_unsat_core_size:                   -1
% 3.12/0.98  bmc1_unsat_core_parents_size:           -1
% 3.12/0.98  bmc1_merge_next_fun:                    0
% 3.12/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.12/0.98  
% 3.12/0.98  ------ Instantiation
% 3.12/0.98  
% 3.12/0.98  inst_num_of_clauses:                    689
% 3.12/0.98  inst_num_in_passive:                    95
% 3.12/0.98  inst_num_in_active:                     398
% 3.12/0.98  inst_num_in_unprocessed:                196
% 3.12/0.98  inst_num_of_loops:                      590
% 3.12/0.98  inst_num_of_learning_restarts:          0
% 3.12/0.98  inst_num_moves_active_passive:          189
% 3.12/0.98  inst_lit_activity:                      0
% 3.12/0.98  inst_lit_activity_moves:                0
% 3.12/0.98  inst_num_tautologies:                   0
% 3.12/0.98  inst_num_prop_implied:                  0
% 3.12/0.98  inst_num_existing_simplified:           0
% 3.12/0.98  inst_num_eq_res_simplified:             0
% 3.12/0.98  inst_num_child_elim:                    0
% 3.12/0.98  inst_num_of_dismatching_blockings:      152
% 3.12/0.98  inst_num_of_non_proper_insts:           612
% 3.12/0.98  inst_num_of_duplicates:                 0
% 3.12/0.98  inst_inst_num_from_inst_to_res:         0
% 3.12/0.98  inst_dismatching_checking_time:         0.
% 3.12/0.98  
% 3.12/0.98  ------ Resolution
% 3.12/0.98  
% 3.12/0.98  res_num_of_clauses:                     0
% 3.12/0.98  res_num_in_passive:                     0
% 3.12/0.98  res_num_in_active:                      0
% 3.12/0.98  res_num_of_loops:                       162
% 3.12/0.98  res_forward_subset_subsumed:            29
% 3.12/0.98  res_backward_subset_subsumed:           0
% 3.12/0.98  res_forward_subsumed:                   0
% 3.12/0.98  res_backward_subsumed:                  0
% 3.12/0.98  res_forward_subsumption_resolution:     5
% 3.12/0.98  res_backward_subsumption_resolution:    0
% 3.12/0.98  res_clause_to_clause_subsumption:       370
% 3.12/0.98  res_orphan_elimination:                 0
% 3.12/0.98  res_tautology_del:                      63
% 3.12/0.98  res_num_eq_res_simplified:              0
% 3.12/0.98  res_num_sel_changes:                    0
% 3.12/0.98  res_moves_from_active_to_pass:          0
% 3.12/0.98  
% 3.12/0.98  ------ Superposition
% 3.12/0.98  
% 3.12/0.98  sup_time_total:                         0.
% 3.12/0.98  sup_time_generating:                    0.
% 3.12/0.98  sup_time_sim_full:                      0.
% 3.12/0.98  sup_time_sim_immed:                     0.
% 3.12/0.98  
% 3.12/0.98  sup_num_of_clauses:                     124
% 3.12/0.98  sup_num_in_active:                      64
% 3.12/0.98  sup_num_in_passive:                     60
% 3.12/0.98  sup_num_of_loops:                       116
% 3.12/0.98  sup_fw_superposition:                   102
% 3.12/0.98  sup_bw_superposition:                   61
% 3.12/0.98  sup_immediate_simplified:               69
% 3.12/0.98  sup_given_eliminated:                   0
% 3.12/0.98  comparisons_done:                       0
% 3.12/0.98  comparisons_avoided:                    17
% 3.12/0.98  
% 3.12/0.98  ------ Simplifications
% 3.12/0.98  
% 3.12/0.98  
% 3.12/0.98  sim_fw_subset_subsumed:                 16
% 3.12/0.98  sim_bw_subset_subsumed:                 5
% 3.12/0.98  sim_fw_subsumed:                        12
% 3.12/0.98  sim_bw_subsumed:                        4
% 3.12/0.98  sim_fw_subsumption_res:                 2
% 3.12/0.98  sim_bw_subsumption_res:                 3
% 3.12/0.98  sim_tautology_del:                      4
% 3.12/0.98  sim_eq_tautology_del:                   9
% 3.12/0.98  sim_eq_res_simp:                        3
% 3.12/0.98  sim_fw_demodulated:                     26
% 3.12/0.98  sim_bw_demodulated:                     52
% 3.12/0.98  sim_light_normalised:                   36
% 3.12/0.98  sim_joinable_taut:                      0
% 3.12/0.98  sim_joinable_simp:                      0
% 3.12/0.98  sim_ac_normalised:                      0
% 3.12/0.98  sim_smt_subsumption:                    0
% 3.12/0.98  
%------------------------------------------------------------------------------
