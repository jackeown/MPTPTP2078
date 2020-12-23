%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:41 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  239 (10174 expanded)
%              Number of clauses        :  170 (3143 expanded)
%              Number of leaves         :   22 (2018 expanded)
%              Depth                    :   24
%              Number of atoms          :  705 (55023 expanded)
%              Number of equality atoms :  394 (10884 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f50,plain,
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

fof(f51,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
      | ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
      | ~ v1_funct_1(k2_funct_1(sK5)) )
    & k2_relset_1(sK3,sK4,sK5) = sK4
    & v2_funct_1(sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f50])).

fof(f86,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    k2_relset_1(sK3,sK4,sK5) = sK4 ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f85,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f82,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
    | ~ v1_funct_1(k2_funct_1(sK5)) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,(
    v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f65,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f45])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f72])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1363,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_435,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | v1_xboole_0(X3)
    | X2 != X3
    | sK0(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X0),X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_1359,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK0(X0),X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_3900,plain,
    ( m1_subset_1(sK0(sK5),k2_zfmisc_1(sK3,sK4)) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_1359])).

cnf(c_40,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_123,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1679,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1680,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1679])).

cnf(c_793,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2277,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_2278,plain,
    ( sK5 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2277])).

cnf(c_2280,plain,
    ( sK5 != k1_xboole_0
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2278])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1368,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2520,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1363,c_1368])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(sK3,sK4,sK5) = sK4 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2522,plain,
    ( k2_relat_1(sK5) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_2520,c_33])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1377,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2564,plain,
    ( sK4 != k1_xboole_0
    | sK5 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2522,c_1377])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_675,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X1
    | sK4 != X2
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_36])).

cnf(c_676,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_675])).

cnf(c_678,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_676,c_35])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1369,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2571,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1363,c_1369])).

cnf(c_2598,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_678,c_2571])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
    | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_699,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK5))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK5) != X0
    | k1_relat_1(X0) != sK4
    | k2_relat_1(X0) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_32])).

cnf(c_700,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | ~ v1_relat_1(k2_funct_1(sK5))
    | k1_relat_1(k2_funct_1(sK5)) != sK4
    | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
    inference(unflattening,[status(thm)],[c_699])).

cnf(c_712,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relat_1(k2_funct_1(sK5)) != sK4
    | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_700,c_15])).

cnf(c_1348,plain,
    ( k1_relat_1(k2_funct_1(sK5)) != sK4
    | k2_relat_1(k2_funct_1(sK5)) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_38,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_701,plain,
    ( k1_relat_1(k2_funct_1(sK5)) != sK4
    | k2_relat_1(k2_funct_1(sK5)) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1655,plain,
    ( v1_funct_1(k2_funct_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1656,plain,
    ( v1_funct_1(k2_funct_1(sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1655])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1668,plain,
    ( ~ v1_funct_1(sK5)
    | v1_relat_1(k2_funct_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1669,plain,
    ( v1_funct_1(sK5) != iProver_top
    | v1_relat_1(k2_funct_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1668])).

cnf(c_1969,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | k2_relat_1(k2_funct_1(sK5)) != sK3
    | k1_relat_1(k2_funct_1(sK5)) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1348,c_38,c_40,c_701,c_1656,c_1669,c_1680])).

cnf(c_1970,plain,
    ( k1_relat_1(k2_funct_1(sK5)) != sK4
    | k2_relat_1(k2_funct_1(sK5)) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1969])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_34,negated_conjecture,
    ( v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_413,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_34])).

cnf(c_414,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_416,plain,
    ( ~ v1_relat_1(sK5)
    | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_414,c_37])).

cnf(c_1360,plain,
    ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_1684,plain,
    ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1360,c_37,c_35,c_414,c_1679])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_399,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_34])).

cnf(c_400,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_402,plain,
    ( ~ v1_relat_1(sK5)
    | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_400,c_37])).

cnf(c_1361,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_1688,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1361,c_37,c_35,c_400,c_1679])).

cnf(c_1973,plain,
    ( k1_relat_1(sK5) != sK3
    | k2_relat_1(sK5) != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1970,c_1684,c_1688])).

cnf(c_2546,plain,
    ( k1_relat_1(sK5) != sK3
    | sK4 != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2522,c_1973])).

cnf(c_2550,plain,
    ( k1_relat_1(sK5) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2546])).

cnf(c_2796,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2598,c_2550])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1364,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3147,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK5)),k1_relat_1(sK5)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1684,c_1364])).

cnf(c_2547,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = sK4 ),
    inference(demodulation,[status(thm)],[c_2522,c_1688])).

cnf(c_3184,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k1_relat_1(sK5)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3147,c_2547])).

cnf(c_3858,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k1_relat_1(sK5)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3184,c_38,c_40,c_1656,c_1669,c_1680])).

cnf(c_3863,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2598,c_3858])).

cnf(c_4070,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3900,c_40,c_123,c_1680,c_2280,c_2564,c_2796,c_3863])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_448,plain,
    ( ~ v1_xboole_0(X0)
    | X1 != X0
    | sK1(X1) != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_449,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_1358,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_4075,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4070,c_1358])).

cnf(c_22,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_659,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK5) != X0
    | sK3 != X2
    | sK4 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_660,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != sK4
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_659])).

cnf(c_1350,plain,
    ( k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != sK4
    | k1_xboole_0 = sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_661,plain,
    ( k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != sK4
    | k1_xboole_0 = sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_1850,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | k1_xboole_0 = sK3
    | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1350,c_38,c_40,c_661,c_1656,c_1680])).

cnf(c_1851,plain,
    ( k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != sK4
    | k1_xboole_0 = sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1850])).

cnf(c_4098,plain,
    ( k1_relset_1(sK4,sK3,k2_funct_1(k1_xboole_0)) != sK4
    | sK3 = k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4075,c_1851])).

cnf(c_451,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_449])).

cnf(c_718,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k2_funct_1(sK5) != sK5
    | sK3 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_36])).

cnf(c_1347,plain,
    ( k2_funct_1(sK5) != sK5
    | sK3 != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_719,plain,
    ( k2_funct_1(sK5) != sK5
    | sK3 != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_1799,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | sK3 != sK4
    | k2_funct_1(sK5) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1347,c_38,c_40,c_719,c_1656,c_1680])).

cnf(c_1800,plain,
    ( k2_funct_1(sK5) != sK5
    | sK3 != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1799])).

cnf(c_792,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1839,plain,
    ( sK3 != X0
    | sK3 = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_1840,plain,
    ( sK3 = sK4
    | sK3 != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1839])).

cnf(c_1862,plain,
    ( ~ v1_xboole_0(sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_449])).

cnf(c_1865,plain,
    ( k1_xboole_0 = sK5
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1862])).

cnf(c_791,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1891,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_1846,plain,
    ( k1_relat_1(sK5) != X0
    | k1_relat_1(sK5) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_1996,plain,
    ( k1_relat_1(sK5) != k1_relat_1(X0)
    | k1_relat_1(sK5) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1846])).

cnf(c_1998,plain,
    ( k1_relat_1(sK5) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(sK5) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1996])).

cnf(c_798,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_1997,plain,
    ( k1_relat_1(sK5) = k1_relat_1(X0)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_1999,plain,
    ( k1_relat_1(sK5) = k1_relat_1(k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1997])).

cnf(c_2647,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_2648,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2647])).

cnf(c_2797,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2796])).

cnf(c_2347,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_2964,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2347])).

cnf(c_2965,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2964])).

cnf(c_795,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1783,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_2182,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | X0 != k1_xboole_0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1783])).

cnf(c_3216,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | k2_funct_1(sK5) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_2182])).

cnf(c_3217,plain,
    ( k2_funct_1(sK5) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3216])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1672,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3615,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(instantiation,[status(thm)],[c_1672])).

cnf(c_3616,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3615])).

cnf(c_3650,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) ),
    inference(instantiation,[status(thm)],[c_1672])).

cnf(c_3651,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3650])).

cnf(c_2513,plain,
    ( k2_funct_1(sK5) = k1_xboole_0
    | k1_relat_1(sK5) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1684,c_1377])).

cnf(c_2514,plain,
    ( ~ v1_relat_1(k2_funct_1(sK5))
    | k2_funct_1(sK5) = k1_xboole_0
    | k1_relat_1(sK5) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2513])).

cnf(c_3692,plain,
    ( k1_relat_1(sK5) != k1_xboole_0
    | k2_funct_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2513,c_37,c_35,c_1668,c_1679,c_2514])).

cnf(c_3693,plain,
    ( k2_funct_1(sK5) = k1_xboole_0
    | k1_relat_1(sK5) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3692])).

cnf(c_1877,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_4377,plain,
    ( k2_funct_1(sK5) != X0
    | k2_funct_1(sK5) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1877])).

cnf(c_4378,plain,
    ( k2_funct_1(sK5) = sK5
    | k2_funct_1(sK5) != k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4377])).

cnf(c_2183,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_3472,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_2183])).

cnf(c_4741,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_3472])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1376,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2382,plain,
    ( k2_funct_1(sK5) = k1_xboole_0
    | k2_relat_1(sK5) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1688,c_1376])).

cnf(c_2383,plain,
    ( ~ v1_relat_1(k2_funct_1(sK5))
    | k2_funct_1(sK5) = k1_xboole_0
    | k2_relat_1(sK5) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2382])).

cnf(c_2439,plain,
    ( k2_relat_1(sK5) != k1_xboole_0
    | k2_funct_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2382,c_37,c_35,c_1668,c_1679,c_2383])).

cnf(c_2440,plain,
    ( k2_funct_1(sK5) = k1_xboole_0
    | k2_relat_1(sK5) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2439])).

cnf(c_2544,plain,
    ( k2_funct_1(sK5) = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2522,c_2440])).

cnf(c_4090,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4075,c_2544])).

cnf(c_4834,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4090,c_2796,c_3863])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_569,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_relat_1(X2) != k1_xboole_0
    | k2_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_570,c_15])).

cnf(c_1354,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_584])).

cnf(c_2448,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK5)),k2_funct_1(sK5)) = k1_xboole_0
    | k2_relat_1(sK5) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK5))))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1688,c_1354])).

cnf(c_2449,plain,
    ( k1_relset_1(k1_xboole_0,k1_relat_1(sK5),k2_funct_1(sK5)) = k1_xboole_0
    | k2_relat_1(sK5) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK5)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2448,c_1684])).

cnf(c_2585,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK5)),k2_funct_1(sK5)) = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK5))))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2547,c_1354])).

cnf(c_2591,plain,
    ( k1_relset_1(k1_xboole_0,k1_relat_1(sK5),k2_funct_1(sK5)) = k1_xboole_0
    | sK4 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK5)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2585,c_1684])).

cnf(c_4525,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK5)))) != iProver_top
    | k1_relset_1(k1_xboole_0,k1_relat_1(sK5),k2_funct_1(sK5)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2449,c_38,c_40,c_1656,c_1680,c_2591,c_2796,c_3863])).

cnf(c_4526,plain,
    ( k1_relset_1(k1_xboole_0,k1_relat_1(sK5),k2_funct_1(sK5)) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK5)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4525])).

cnf(c_4529,plain,
    ( k1_relset_1(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4526,c_4075])).

cnf(c_4840,plain,
    ( k1_relset_1(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4834,c_4529])).

cnf(c_4092,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = sK4 ),
    inference(demodulation,[status(thm)],[c_4075,c_2547])).

cnf(c_4842,plain,
    ( k1_relat_1(k1_xboole_0) = sK4 ),
    inference(demodulation,[status(thm)],[c_4834,c_4092])).

cnf(c_4847,plain,
    ( k1_relset_1(k1_xboole_0,sK4,k1_xboole_0) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4840,c_4842])).

cnf(c_1378,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2569,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1378,c_1369])).

cnf(c_4850,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4847,c_2569])).

cnf(c_4956,plain,
    ( k1_relset_1(sK4,sK3,k2_funct_1(k1_xboole_0)) != sK4
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4098,c_37,c_35,c_40,c_718,c_1655,c_1679,c_1680,c_1840,c_2544,c_2564,c_2796,c_3216,c_3615,c_3863,c_4378,c_4741])).

cnf(c_4960,plain,
    ( k1_relset_1(sK4,sK3,k1_xboole_0) != sK4
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4956,c_4834])).

cnf(c_4961,plain,
    ( k1_relat_1(k1_xboole_0) != sK4
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4960,c_2569])).

cnf(c_4964,plain,
    ( k1_relat_1(k1_xboole_0) != sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4961,c_1378])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4964,c_4842])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:20:52 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.01/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.01  
% 3.01/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/1.01  
% 3.01/1.01  ------  iProver source info
% 3.01/1.01  
% 3.01/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.01/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/1.01  git: non_committed_changes: false
% 3.01/1.01  git: last_make_outside_of_git: false
% 3.01/1.01  
% 3.01/1.01  ------ 
% 3.01/1.01  
% 3.01/1.01  ------ Input Options
% 3.01/1.01  
% 3.01/1.01  --out_options                           all
% 3.01/1.01  --tptp_safe_out                         true
% 3.01/1.01  --problem_path                          ""
% 3.01/1.01  --include_path                          ""
% 3.01/1.01  --clausifier                            res/vclausify_rel
% 3.01/1.01  --clausifier_options                    --mode clausify
% 3.01/1.01  --stdin                                 false
% 3.01/1.01  --stats_out                             all
% 3.01/1.01  
% 3.01/1.01  ------ General Options
% 3.01/1.01  
% 3.01/1.01  --fof                                   false
% 3.01/1.01  --time_out_real                         305.
% 3.01/1.01  --time_out_virtual                      -1.
% 3.01/1.01  --symbol_type_check                     false
% 3.01/1.01  --clausify_out                          false
% 3.01/1.01  --sig_cnt_out                           false
% 3.01/1.01  --trig_cnt_out                          false
% 3.01/1.01  --trig_cnt_out_tolerance                1.
% 3.01/1.01  --trig_cnt_out_sk_spl                   false
% 3.01/1.01  --abstr_cl_out                          false
% 3.01/1.01  
% 3.01/1.01  ------ Global Options
% 3.01/1.01  
% 3.01/1.01  --schedule                              default
% 3.01/1.01  --add_important_lit                     false
% 3.01/1.01  --prop_solver_per_cl                    1000
% 3.01/1.01  --min_unsat_core                        false
% 3.01/1.01  --soft_assumptions                      false
% 3.01/1.01  --soft_lemma_size                       3
% 3.01/1.01  --prop_impl_unit_size                   0
% 3.01/1.01  --prop_impl_unit                        []
% 3.01/1.01  --share_sel_clauses                     true
% 3.01/1.01  --reset_solvers                         false
% 3.01/1.01  --bc_imp_inh                            [conj_cone]
% 3.01/1.01  --conj_cone_tolerance                   3.
% 3.01/1.01  --extra_neg_conj                        none
% 3.01/1.01  --large_theory_mode                     true
% 3.01/1.01  --prolific_symb_bound                   200
% 3.01/1.01  --lt_threshold                          2000
% 3.01/1.01  --clause_weak_htbl                      true
% 3.01/1.01  --gc_record_bc_elim                     false
% 3.01/1.01  
% 3.01/1.01  ------ Preprocessing Options
% 3.01/1.01  
% 3.01/1.01  --preprocessing_flag                    true
% 3.01/1.01  --time_out_prep_mult                    0.1
% 3.01/1.01  --splitting_mode                        input
% 3.01/1.01  --splitting_grd                         true
% 3.01/1.01  --splitting_cvd                         false
% 3.01/1.01  --splitting_cvd_svl                     false
% 3.01/1.01  --splitting_nvd                         32
% 3.01/1.01  --sub_typing                            true
% 3.01/1.01  --prep_gs_sim                           true
% 3.01/1.01  --prep_unflatten                        true
% 3.01/1.01  --prep_res_sim                          true
% 3.01/1.01  --prep_upred                            true
% 3.01/1.01  --prep_sem_filter                       exhaustive
% 3.01/1.01  --prep_sem_filter_out                   false
% 3.01/1.01  --pred_elim                             true
% 3.01/1.01  --res_sim_input                         true
% 3.01/1.01  --eq_ax_congr_red                       true
% 3.01/1.01  --pure_diseq_elim                       true
% 3.01/1.01  --brand_transform                       false
% 3.01/1.01  --non_eq_to_eq                          false
% 3.01/1.01  --prep_def_merge                        true
% 3.01/1.01  --prep_def_merge_prop_impl              false
% 3.01/1.01  --prep_def_merge_mbd                    true
% 3.01/1.01  --prep_def_merge_tr_red                 false
% 3.01/1.01  --prep_def_merge_tr_cl                  false
% 3.01/1.01  --smt_preprocessing                     true
% 3.01/1.01  --smt_ac_axioms                         fast
% 3.01/1.01  --preprocessed_out                      false
% 3.01/1.01  --preprocessed_stats                    false
% 3.01/1.01  
% 3.01/1.01  ------ Abstraction refinement Options
% 3.01/1.01  
% 3.01/1.01  --abstr_ref                             []
% 3.01/1.01  --abstr_ref_prep                        false
% 3.01/1.01  --abstr_ref_until_sat                   false
% 3.01/1.01  --abstr_ref_sig_restrict                funpre
% 3.01/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/1.01  --abstr_ref_under                       []
% 3.01/1.01  
% 3.01/1.01  ------ SAT Options
% 3.01/1.01  
% 3.01/1.01  --sat_mode                              false
% 3.01/1.01  --sat_fm_restart_options                ""
% 3.01/1.01  --sat_gr_def                            false
% 3.01/1.01  --sat_epr_types                         true
% 3.01/1.01  --sat_non_cyclic_types                  false
% 3.01/1.01  --sat_finite_models                     false
% 3.01/1.01  --sat_fm_lemmas                         false
% 3.01/1.01  --sat_fm_prep                           false
% 3.01/1.01  --sat_fm_uc_incr                        true
% 3.01/1.01  --sat_out_model                         small
% 3.01/1.01  --sat_out_clauses                       false
% 3.01/1.01  
% 3.01/1.01  ------ QBF Options
% 3.01/1.01  
% 3.01/1.01  --qbf_mode                              false
% 3.01/1.01  --qbf_elim_univ                         false
% 3.01/1.01  --qbf_dom_inst                          none
% 3.01/1.01  --qbf_dom_pre_inst                      false
% 3.01/1.01  --qbf_sk_in                             false
% 3.01/1.01  --qbf_pred_elim                         true
% 3.01/1.01  --qbf_split                             512
% 3.01/1.01  
% 3.01/1.01  ------ BMC1 Options
% 3.01/1.01  
% 3.01/1.01  --bmc1_incremental                      false
% 3.01/1.01  --bmc1_axioms                           reachable_all
% 3.01/1.01  --bmc1_min_bound                        0
% 3.01/1.01  --bmc1_max_bound                        -1
% 3.01/1.01  --bmc1_max_bound_default                -1
% 3.01/1.01  --bmc1_symbol_reachability              true
% 3.01/1.01  --bmc1_property_lemmas                  false
% 3.01/1.01  --bmc1_k_induction                      false
% 3.01/1.01  --bmc1_non_equiv_states                 false
% 3.01/1.01  --bmc1_deadlock                         false
% 3.01/1.01  --bmc1_ucm                              false
% 3.01/1.01  --bmc1_add_unsat_core                   none
% 3.01/1.01  --bmc1_unsat_core_children              false
% 3.01/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/1.01  --bmc1_out_stat                         full
% 3.01/1.01  --bmc1_ground_init                      false
% 3.01/1.01  --bmc1_pre_inst_next_state              false
% 3.01/1.01  --bmc1_pre_inst_state                   false
% 3.01/1.01  --bmc1_pre_inst_reach_state             false
% 3.01/1.01  --bmc1_out_unsat_core                   false
% 3.01/1.01  --bmc1_aig_witness_out                  false
% 3.01/1.01  --bmc1_verbose                          false
% 3.01/1.01  --bmc1_dump_clauses_tptp                false
% 3.01/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.01/1.01  --bmc1_dump_file                        -
% 3.01/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.01  --bmc1_ucm_extend_mode                  1
% 3.01/1.01  --bmc1_ucm_init_mode                    2
% 3.01/1.01  --bmc1_ucm_cone_mode                    none
% 3.01/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.01  --bmc1_ucm_relax_model                  4
% 3.01/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.01  --bmc1_ucm_layered_model                none
% 3.01/1.01  --bmc1_ucm_max_lemma_size               10
% 3.01/1.01  
% 3.01/1.01  ------ AIG Options
% 3.01/1.01  
% 3.01/1.01  --aig_mode                              false
% 3.01/1.01  
% 3.01/1.01  ------ Instantiation Options
% 3.01/1.01  
% 3.01/1.01  --instantiation_flag                    true
% 3.01/1.01  --inst_sos_flag                         false
% 3.01/1.01  --inst_sos_phase                        true
% 3.01/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.01  --inst_lit_sel_side                     num_symb
% 3.01/1.01  --inst_solver_per_active                1400
% 3.01/1.01  --inst_solver_calls_frac                1.
% 3.01/1.01  --inst_passive_queue_type               priority_queues
% 3.01/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/1.01  --inst_passive_queues_freq              [25;2]
% 3.01/1.01  --inst_dismatching                      true
% 3.01/1.01  --inst_eager_unprocessed_to_passive     true
% 3.01/1.01  --inst_prop_sim_given                   true
% 3.01/1.01  --inst_prop_sim_new                     false
% 3.01/1.01  --inst_subs_new                         false
% 3.01/1.01  --inst_eq_res_simp                      false
% 3.01/1.01  --inst_subs_given                       false
% 3.01/1.01  --inst_orphan_elimination               true
% 3.01/1.01  --inst_learning_loop_flag               true
% 3.01/1.01  --inst_learning_start                   3000
% 3.01/1.01  --inst_learning_factor                  2
% 3.01/1.01  --inst_start_prop_sim_after_learn       3
% 3.01/1.01  --inst_sel_renew                        solver
% 3.01/1.01  --inst_lit_activity_flag                true
% 3.01/1.01  --inst_restr_to_given                   false
% 3.01/1.01  --inst_activity_threshold               500
% 3.01/1.01  --inst_out_proof                        true
% 3.01/1.01  
% 3.01/1.01  ------ Resolution Options
% 3.01/1.01  
% 3.01/1.01  --resolution_flag                       true
% 3.01/1.01  --res_lit_sel                           adaptive
% 3.01/1.01  --res_lit_sel_side                      none
% 3.01/1.01  --res_ordering                          kbo
% 3.01/1.01  --res_to_prop_solver                    active
% 3.01/1.01  --res_prop_simpl_new                    false
% 3.01/1.01  --res_prop_simpl_given                  true
% 3.01/1.01  --res_passive_queue_type                priority_queues
% 3.01/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/1.01  --res_passive_queues_freq               [15;5]
% 3.01/1.01  --res_forward_subs                      full
% 3.01/1.01  --res_backward_subs                     full
% 3.01/1.01  --res_forward_subs_resolution           true
% 3.01/1.01  --res_backward_subs_resolution          true
% 3.01/1.01  --res_orphan_elimination                true
% 3.01/1.01  --res_time_limit                        2.
% 3.01/1.01  --res_out_proof                         true
% 3.01/1.01  
% 3.01/1.01  ------ Superposition Options
% 3.01/1.01  
% 3.01/1.01  --superposition_flag                    true
% 3.01/1.01  --sup_passive_queue_type                priority_queues
% 3.01/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.01  --demod_completeness_check              fast
% 3.01/1.01  --demod_use_ground                      true
% 3.01/1.01  --sup_to_prop_solver                    passive
% 3.01/1.01  --sup_prop_simpl_new                    true
% 3.01/1.01  --sup_prop_simpl_given                  true
% 3.01/1.01  --sup_fun_splitting                     false
% 3.01/1.01  --sup_smt_interval                      50000
% 3.01/1.01  
% 3.01/1.01  ------ Superposition Simplification Setup
% 3.01/1.01  
% 3.01/1.01  --sup_indices_passive                   []
% 3.01/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.01  --sup_full_bw                           [BwDemod]
% 3.01/1.01  --sup_immed_triv                        [TrivRules]
% 3.01/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.01  --sup_immed_bw_main                     []
% 3.01/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.01  
% 3.01/1.01  ------ Combination Options
% 3.01/1.01  
% 3.01/1.01  --comb_res_mult                         3
% 3.01/1.01  --comb_sup_mult                         2
% 3.01/1.01  --comb_inst_mult                        10
% 3.01/1.01  
% 3.01/1.01  ------ Debug Options
% 3.01/1.01  
% 3.01/1.01  --dbg_backtrace                         false
% 3.01/1.01  --dbg_dump_prop_clauses                 false
% 3.01/1.01  --dbg_dump_prop_clauses_file            -
% 3.01/1.01  --dbg_out_stat                          false
% 3.01/1.01  ------ Parsing...
% 3.01/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/1.01  
% 3.01/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.01/1.01  
% 3.01/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/1.01  
% 3.01/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.01  ------ Proving...
% 3.01/1.01  ------ Problem Properties 
% 3.01/1.01  
% 3.01/1.01  
% 3.01/1.01  clauses                                 39
% 3.01/1.01  conjectures                             3
% 3.01/1.01  EPR                                     3
% 3.01/1.01  Horn                                    32
% 3.01/1.01  unary                                   12
% 3.01/1.01  binary                                  9
% 3.01/1.01  lits                                    94
% 3.01/1.01  lits eq                                 40
% 3.01/1.01  fd_pure                                 0
% 3.01/1.01  fd_pseudo                               0
% 3.01/1.01  fd_cond                                 5
% 3.01/1.01  fd_pseudo_cond                          0
% 3.01/1.01  AC symbols                              0
% 3.01/1.01  
% 3.01/1.01  ------ Schedule dynamic 5 is on 
% 3.01/1.01  
% 3.01/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.01/1.01  
% 3.01/1.01  
% 3.01/1.01  ------ 
% 3.01/1.01  Current options:
% 3.01/1.01  ------ 
% 3.01/1.01  
% 3.01/1.01  ------ Input Options
% 3.01/1.01  
% 3.01/1.01  --out_options                           all
% 3.01/1.01  --tptp_safe_out                         true
% 3.01/1.01  --problem_path                          ""
% 3.01/1.01  --include_path                          ""
% 3.01/1.01  --clausifier                            res/vclausify_rel
% 3.01/1.01  --clausifier_options                    --mode clausify
% 3.01/1.01  --stdin                                 false
% 3.01/1.01  --stats_out                             all
% 3.01/1.01  
% 3.01/1.01  ------ General Options
% 3.01/1.01  
% 3.01/1.01  --fof                                   false
% 3.01/1.01  --time_out_real                         305.
% 3.01/1.01  --time_out_virtual                      -1.
% 3.01/1.01  --symbol_type_check                     false
% 3.01/1.01  --clausify_out                          false
% 3.01/1.01  --sig_cnt_out                           false
% 3.01/1.01  --trig_cnt_out                          false
% 3.01/1.01  --trig_cnt_out_tolerance                1.
% 3.01/1.01  --trig_cnt_out_sk_spl                   false
% 3.01/1.01  --abstr_cl_out                          false
% 3.01/1.01  
% 3.01/1.01  ------ Global Options
% 3.01/1.01  
% 3.01/1.01  --schedule                              default
% 3.01/1.01  --add_important_lit                     false
% 3.01/1.01  --prop_solver_per_cl                    1000
% 3.01/1.01  --min_unsat_core                        false
% 3.01/1.01  --soft_assumptions                      false
% 3.01/1.01  --soft_lemma_size                       3
% 3.01/1.01  --prop_impl_unit_size                   0
% 3.01/1.01  --prop_impl_unit                        []
% 3.01/1.01  --share_sel_clauses                     true
% 3.01/1.01  --reset_solvers                         false
% 3.01/1.01  --bc_imp_inh                            [conj_cone]
% 3.01/1.01  --conj_cone_tolerance                   3.
% 3.01/1.01  --extra_neg_conj                        none
% 3.01/1.01  --large_theory_mode                     true
% 3.01/1.01  --prolific_symb_bound                   200
% 3.01/1.01  --lt_threshold                          2000
% 3.01/1.01  --clause_weak_htbl                      true
% 3.01/1.01  --gc_record_bc_elim                     false
% 3.01/1.01  
% 3.01/1.01  ------ Preprocessing Options
% 3.01/1.01  
% 3.01/1.01  --preprocessing_flag                    true
% 3.01/1.01  --time_out_prep_mult                    0.1
% 3.01/1.01  --splitting_mode                        input
% 3.01/1.01  --splitting_grd                         true
% 3.01/1.01  --splitting_cvd                         false
% 3.01/1.01  --splitting_cvd_svl                     false
% 3.01/1.01  --splitting_nvd                         32
% 3.01/1.01  --sub_typing                            true
% 3.01/1.01  --prep_gs_sim                           true
% 3.01/1.01  --prep_unflatten                        true
% 3.01/1.01  --prep_res_sim                          true
% 3.01/1.01  --prep_upred                            true
% 3.01/1.01  --prep_sem_filter                       exhaustive
% 3.01/1.01  --prep_sem_filter_out                   false
% 3.01/1.01  --pred_elim                             true
% 3.01/1.01  --res_sim_input                         true
% 3.01/1.01  --eq_ax_congr_red                       true
% 3.01/1.01  --pure_diseq_elim                       true
% 3.01/1.01  --brand_transform                       false
% 3.01/1.01  --non_eq_to_eq                          false
% 3.01/1.01  --prep_def_merge                        true
% 3.01/1.01  --prep_def_merge_prop_impl              false
% 3.01/1.01  --prep_def_merge_mbd                    true
% 3.01/1.01  --prep_def_merge_tr_red                 false
% 3.01/1.01  --prep_def_merge_tr_cl                  false
% 3.01/1.01  --smt_preprocessing                     true
% 3.01/1.01  --smt_ac_axioms                         fast
% 3.01/1.01  --preprocessed_out                      false
% 3.01/1.01  --preprocessed_stats                    false
% 3.01/1.01  
% 3.01/1.01  ------ Abstraction refinement Options
% 3.01/1.01  
% 3.01/1.01  --abstr_ref                             []
% 3.01/1.01  --abstr_ref_prep                        false
% 3.01/1.01  --abstr_ref_until_sat                   false
% 3.01/1.01  --abstr_ref_sig_restrict                funpre
% 3.01/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/1.01  --abstr_ref_under                       []
% 3.01/1.01  
% 3.01/1.01  ------ SAT Options
% 3.01/1.01  
% 3.01/1.01  --sat_mode                              false
% 3.01/1.01  --sat_fm_restart_options                ""
% 3.01/1.01  --sat_gr_def                            false
% 3.01/1.01  --sat_epr_types                         true
% 3.01/1.01  --sat_non_cyclic_types                  false
% 3.01/1.01  --sat_finite_models                     false
% 3.01/1.01  --sat_fm_lemmas                         false
% 3.01/1.01  --sat_fm_prep                           false
% 3.01/1.01  --sat_fm_uc_incr                        true
% 3.01/1.01  --sat_out_model                         small
% 3.01/1.01  --sat_out_clauses                       false
% 3.01/1.01  
% 3.01/1.01  ------ QBF Options
% 3.01/1.01  
% 3.01/1.01  --qbf_mode                              false
% 3.01/1.01  --qbf_elim_univ                         false
% 3.01/1.01  --qbf_dom_inst                          none
% 3.01/1.01  --qbf_dom_pre_inst                      false
% 3.01/1.01  --qbf_sk_in                             false
% 3.01/1.01  --qbf_pred_elim                         true
% 3.01/1.01  --qbf_split                             512
% 3.01/1.01  
% 3.01/1.01  ------ BMC1 Options
% 3.01/1.01  
% 3.01/1.01  --bmc1_incremental                      false
% 3.01/1.01  --bmc1_axioms                           reachable_all
% 3.01/1.01  --bmc1_min_bound                        0
% 3.01/1.01  --bmc1_max_bound                        -1
% 3.01/1.01  --bmc1_max_bound_default                -1
% 3.01/1.01  --bmc1_symbol_reachability              true
% 3.01/1.01  --bmc1_property_lemmas                  false
% 3.01/1.01  --bmc1_k_induction                      false
% 3.01/1.01  --bmc1_non_equiv_states                 false
% 3.01/1.01  --bmc1_deadlock                         false
% 3.01/1.01  --bmc1_ucm                              false
% 3.01/1.01  --bmc1_add_unsat_core                   none
% 3.01/1.01  --bmc1_unsat_core_children              false
% 3.01/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/1.01  --bmc1_out_stat                         full
% 3.01/1.01  --bmc1_ground_init                      false
% 3.01/1.01  --bmc1_pre_inst_next_state              false
% 3.01/1.01  --bmc1_pre_inst_state                   false
% 3.01/1.01  --bmc1_pre_inst_reach_state             false
% 3.01/1.01  --bmc1_out_unsat_core                   false
% 3.01/1.01  --bmc1_aig_witness_out                  false
% 3.01/1.01  --bmc1_verbose                          false
% 3.01/1.01  --bmc1_dump_clauses_tptp                false
% 3.01/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.01/1.01  --bmc1_dump_file                        -
% 3.01/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.01  --bmc1_ucm_extend_mode                  1
% 3.01/1.01  --bmc1_ucm_init_mode                    2
% 3.01/1.01  --bmc1_ucm_cone_mode                    none
% 3.01/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.01  --bmc1_ucm_relax_model                  4
% 3.01/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.01  --bmc1_ucm_layered_model                none
% 3.01/1.01  --bmc1_ucm_max_lemma_size               10
% 3.01/1.01  
% 3.01/1.01  ------ AIG Options
% 3.01/1.01  
% 3.01/1.01  --aig_mode                              false
% 3.01/1.01  
% 3.01/1.01  ------ Instantiation Options
% 3.01/1.01  
% 3.01/1.01  --instantiation_flag                    true
% 3.01/1.01  --inst_sos_flag                         false
% 3.01/1.01  --inst_sos_phase                        true
% 3.01/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.01  --inst_lit_sel_side                     none
% 3.01/1.01  --inst_solver_per_active                1400
% 3.01/1.01  --inst_solver_calls_frac                1.
% 3.01/1.01  --inst_passive_queue_type               priority_queues
% 3.01/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/1.01  --inst_passive_queues_freq              [25;2]
% 3.01/1.01  --inst_dismatching                      true
% 3.01/1.01  --inst_eager_unprocessed_to_passive     true
% 3.01/1.01  --inst_prop_sim_given                   true
% 3.01/1.01  --inst_prop_sim_new                     false
% 3.01/1.01  --inst_subs_new                         false
% 3.01/1.01  --inst_eq_res_simp                      false
% 3.01/1.01  --inst_subs_given                       false
% 3.01/1.01  --inst_orphan_elimination               true
% 3.01/1.01  --inst_learning_loop_flag               true
% 3.01/1.01  --inst_learning_start                   3000
% 3.01/1.01  --inst_learning_factor                  2
% 3.01/1.01  --inst_start_prop_sim_after_learn       3
% 3.01/1.01  --inst_sel_renew                        solver
% 3.01/1.01  --inst_lit_activity_flag                true
% 3.01/1.01  --inst_restr_to_given                   false
% 3.01/1.01  --inst_activity_threshold               500
% 3.01/1.01  --inst_out_proof                        true
% 3.01/1.01  
% 3.01/1.01  ------ Resolution Options
% 3.01/1.01  
% 3.01/1.01  --resolution_flag                       false
% 3.01/1.01  --res_lit_sel                           adaptive
% 3.01/1.01  --res_lit_sel_side                      none
% 3.01/1.01  --res_ordering                          kbo
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
% 3.01/1.02  fof(f18,conjecture,(
% 3.01/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f19,negated_conjecture,(
% 3.01/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.01/1.02    inference(negated_conjecture,[],[f18])).
% 3.01/1.02  
% 3.01/1.02  fof(f39,plain,(
% 3.01/1.02    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.01/1.02    inference(ennf_transformation,[],[f19])).
% 3.01/1.02  
% 3.01/1.02  fof(f40,plain,(
% 3.01/1.02    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.01/1.02    inference(flattening,[],[f39])).
% 3.01/1.02  
% 3.01/1.02  fof(f50,plain,(
% 3.01/1.02    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) | ~v1_funct_2(k2_funct_1(sK5),sK4,sK3) | ~v1_funct_1(k2_funct_1(sK5))) & k2_relset_1(sK3,sK4,sK5) = sK4 & v2_funct_1(sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 3.01/1.02    introduced(choice_axiom,[])).
% 3.01/1.02  
% 3.01/1.02  fof(f51,plain,(
% 3.01/1.02    (~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) | ~v1_funct_2(k2_funct_1(sK5),sK4,sK3) | ~v1_funct_1(k2_funct_1(sK5))) & k2_relset_1(sK3,sK4,sK5) = sK4 & v2_funct_1(sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 3.01/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f50])).
% 3.01/1.02  
% 3.01/1.02  fof(f86,plain,(
% 3.01/1.02    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.01/1.02    inference(cnf_transformation,[],[f51])).
% 3.01/1.02  
% 3.01/1.02  fof(f1,axiom,(
% 3.01/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f41,plain,(
% 3.01/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.01/1.02    inference(nnf_transformation,[],[f1])).
% 3.01/1.02  
% 3.01/1.02  fof(f42,plain,(
% 3.01/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.01/1.02    inference(rectify,[],[f41])).
% 3.01/1.02  
% 3.01/1.02  fof(f43,plain,(
% 3.01/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.01/1.02    introduced(choice_axiom,[])).
% 3.01/1.02  
% 3.01/1.02  fof(f44,plain,(
% 3.01/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.01/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 3.01/1.02  
% 3.01/1.02  fof(f53,plain,(
% 3.01/1.02    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f44])).
% 3.01/1.02  
% 3.01/1.02  fof(f5,axiom,(
% 3.01/1.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f23,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.01/1.02    inference(ennf_transformation,[],[f5])).
% 3.01/1.02  
% 3.01/1.02  fof(f24,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.01/1.02    inference(flattening,[],[f23])).
% 3.01/1.02  
% 3.01/1.02  fof(f57,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f24])).
% 3.01/1.02  
% 3.01/1.02  fof(f2,axiom,(
% 3.01/1.02    v1_xboole_0(k1_xboole_0)),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f54,plain,(
% 3.01/1.02    v1_xboole_0(k1_xboole_0)),
% 3.01/1.02    inference(cnf_transformation,[],[f2])).
% 3.01/1.02  
% 3.01/1.02  fof(f11,axiom,(
% 3.01/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f31,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.02    inference(ennf_transformation,[],[f11])).
% 3.01/1.02  
% 3.01/1.02  fof(f67,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.02    inference(cnf_transformation,[],[f31])).
% 3.01/1.02  
% 3.01/1.02  fof(f14,axiom,(
% 3.01/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f34,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.02    inference(ennf_transformation,[],[f14])).
% 3.01/1.02  
% 3.01/1.02  fof(f70,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.02    inference(cnf_transformation,[],[f34])).
% 3.01/1.02  
% 3.01/1.02  fof(f88,plain,(
% 3.01/1.02    k2_relset_1(sK3,sK4,sK5) = sK4),
% 3.01/1.02    inference(cnf_transformation,[],[f51])).
% 3.01/1.02  
% 3.01/1.02  fof(f6,axiom,(
% 3.01/1.02    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f25,plain,(
% 3.01/1.02    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.01/1.02    inference(ennf_transformation,[],[f6])).
% 3.01/1.02  
% 3.01/1.02  fof(f26,plain,(
% 3.01/1.02    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.01/1.02    inference(flattening,[],[f25])).
% 3.01/1.02  
% 3.01/1.02  fof(f59,plain,(
% 3.01/1.02    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f26])).
% 3.01/1.02  
% 3.01/1.02  fof(f15,axiom,(
% 3.01/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f35,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.02    inference(ennf_transformation,[],[f15])).
% 3.01/1.02  
% 3.01/1.02  fof(f36,plain,(
% 3.01/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.02    inference(flattening,[],[f35])).
% 3.01/1.02  
% 3.01/1.02  fof(f47,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.02    inference(nnf_transformation,[],[f36])).
% 3.01/1.02  
% 3.01/1.02  fof(f71,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.02    inference(cnf_transformation,[],[f47])).
% 3.01/1.02  
% 3.01/1.02  fof(f85,plain,(
% 3.01/1.02    v1_funct_2(sK5,sK3,sK4)),
% 3.01/1.02    inference(cnf_transformation,[],[f51])).
% 3.01/1.02  
% 3.01/1.02  fof(f13,axiom,(
% 3.01/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f33,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.02    inference(ennf_transformation,[],[f13])).
% 3.01/1.02  
% 3.01/1.02  fof(f69,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.02    inference(cnf_transformation,[],[f33])).
% 3.01/1.02  
% 3.01/1.02  fof(f17,axiom,(
% 3.01/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f37,plain,(
% 3.01/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.01/1.02    inference(ennf_transformation,[],[f17])).
% 3.01/1.02  
% 3.01/1.02  fof(f38,plain,(
% 3.01/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.01/1.02    inference(flattening,[],[f37])).
% 3.01/1.02  
% 3.01/1.02  fof(f82,plain,(
% 3.01/1.02    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f38])).
% 3.01/1.02  
% 3.01/1.02  fof(f89,plain,(
% 3.01/1.02    ~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) | ~v1_funct_2(k2_funct_1(sK5),sK4,sK3) | ~v1_funct_1(k2_funct_1(sK5))),
% 3.01/1.02    inference(cnf_transformation,[],[f51])).
% 3.01/1.02  
% 3.01/1.02  fof(f84,plain,(
% 3.01/1.02    v1_funct_1(sK5)),
% 3.01/1.02    inference(cnf_transformation,[],[f51])).
% 3.01/1.02  
% 3.01/1.02  fof(f8,axiom,(
% 3.01/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f27,plain,(
% 3.01/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.01/1.02    inference(ennf_transformation,[],[f8])).
% 3.01/1.02  
% 3.01/1.02  fof(f28,plain,(
% 3.01/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.01/1.02    inference(flattening,[],[f27])).
% 3.01/1.02  
% 3.01/1.02  fof(f62,plain,(
% 3.01/1.02    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f28])).
% 3.01/1.02  
% 3.01/1.02  fof(f61,plain,(
% 3.01/1.02    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f28])).
% 3.01/1.02  
% 3.01/1.02  fof(f10,axiom,(
% 3.01/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f29,plain,(
% 3.01/1.02    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.01/1.02    inference(ennf_transformation,[],[f10])).
% 3.01/1.02  
% 3.01/1.02  fof(f30,plain,(
% 3.01/1.02    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.01/1.02    inference(flattening,[],[f29])).
% 3.01/1.02  
% 3.01/1.02  fof(f66,plain,(
% 3.01/1.02    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f30])).
% 3.01/1.02  
% 3.01/1.02  fof(f87,plain,(
% 3.01/1.02    v2_funct_1(sK5)),
% 3.01/1.02    inference(cnf_transformation,[],[f51])).
% 3.01/1.02  
% 3.01/1.02  fof(f65,plain,(
% 3.01/1.02    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f30])).
% 3.01/1.02  
% 3.01/1.02  fof(f83,plain,(
% 3.01/1.02    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f38])).
% 3.01/1.02  
% 3.01/1.02  fof(f52,plain,(
% 3.01/1.02    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f44])).
% 3.01/1.02  
% 3.01/1.02  fof(f3,axiom,(
% 3.01/1.02    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f22,plain,(
% 3.01/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.01/1.02    inference(ennf_transformation,[],[f3])).
% 3.01/1.02  
% 3.01/1.02  fof(f45,plain,(
% 3.01/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.01/1.02    introduced(choice_axiom,[])).
% 3.01/1.02  
% 3.01/1.02  fof(f46,plain,(
% 3.01/1.02    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.01/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f45])).
% 3.01/1.02  
% 3.01/1.02  fof(f55,plain,(
% 3.01/1.02    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.01/1.02    inference(cnf_transformation,[],[f46])).
% 3.01/1.02  
% 3.01/1.02  fof(f73,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.02    inference(cnf_transformation,[],[f47])).
% 3.01/1.02  
% 3.01/1.02  fof(f4,axiom,(
% 3.01/1.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f56,plain,(
% 3.01/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.01/1.02    inference(cnf_transformation,[],[f4])).
% 3.01/1.02  
% 3.01/1.02  fof(f58,plain,(
% 3.01/1.02    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f26])).
% 3.01/1.02  
% 3.01/1.02  fof(f72,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.02    inference(cnf_transformation,[],[f47])).
% 3.01/1.02  
% 3.01/1.02  fof(f94,plain,(
% 3.01/1.02    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.01/1.02    inference(equality_resolution,[],[f72])).
% 3.01/1.02  
% 3.01/1.02  cnf(c_35,negated_conjecture,
% 3.01/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.01/1.02      inference(cnf_transformation,[],[f86]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1363,plain,
% 3.01/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_0,plain,
% 3.01/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_5,plain,
% 3.01/1.02      ( m1_subset_1(X0,X1)
% 3.01/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.01/1.02      | ~ r2_hidden(X0,X2) ),
% 3.01/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_435,plain,
% 3.01/1.02      ( m1_subset_1(X0,X1)
% 3.01/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.01/1.02      | v1_xboole_0(X3)
% 3.01/1.02      | X2 != X3
% 3.01/1.02      | sK0(X3) != X0 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_5]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_436,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.01/1.02      | m1_subset_1(sK0(X0),X1)
% 3.01/1.02      | v1_xboole_0(X0) ),
% 3.01/1.02      inference(unflattening,[status(thm)],[c_435]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1359,plain,
% 3.01/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.01/1.02      | m1_subset_1(sK0(X0),X1) = iProver_top
% 3.01/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_436]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3900,plain,
% 3.01/1.02      ( m1_subset_1(sK0(sK5),k2_zfmisc_1(sK3,sK4)) = iProver_top
% 3.01/1.02      | v1_xboole_0(sK5) = iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1363,c_1359]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_40,plain,
% 3.01/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2,plain,
% 3.01/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_123,plain,
% 3.01/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_15,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | v1_relat_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1679,plain,
% 3.01/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.01/1.02      | v1_relat_1(sK5) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_15]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1680,plain,
% 3.01/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.01/1.02      | v1_relat_1(sK5) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_1679]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_793,plain,
% 3.01/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.01/1.02      theory(equality) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2277,plain,
% 3.01/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK5) | sK5 != X0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_793]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2278,plain,
% 3.01/1.02      ( sK5 != X0
% 3.01/1.02      | v1_xboole_0(X0) != iProver_top
% 3.01/1.02      | v1_xboole_0(sK5) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_2277]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2280,plain,
% 3.01/1.02      ( sK5 != k1_xboole_0
% 3.01/1.02      | v1_xboole_0(sK5) = iProver_top
% 3.01/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_2278]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_18,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1368,plain,
% 3.01/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.01/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2520,plain,
% 3.01/1.02      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1363,c_1368]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_33,negated_conjecture,
% 3.01/1.02      ( k2_relset_1(sK3,sK4,sK5) = sK4 ),
% 3.01/1.02      inference(cnf_transformation,[],[f88]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2522,plain,
% 3.01/1.02      ( k2_relat_1(sK5) = sK4 ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_2520,c_33]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_6,plain,
% 3.01/1.02      ( ~ v1_relat_1(X0)
% 3.01/1.02      | k2_relat_1(X0) != k1_xboole_0
% 3.01/1.02      | k1_xboole_0 = X0 ),
% 3.01/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1377,plain,
% 3.01/1.02      ( k2_relat_1(X0) != k1_xboole_0
% 3.01/1.02      | k1_xboole_0 = X0
% 3.01/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2564,plain,
% 3.01/1.02      ( sK4 != k1_xboole_0
% 3.01/1.02      | sK5 = k1_xboole_0
% 3.01/1.02      | v1_relat_1(sK5) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_2522,c_1377]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_24,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.01/1.02      | k1_xboole_0 = X2 ),
% 3.01/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_36,negated_conjecture,
% 3.01/1.02      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.01/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_675,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.01/1.02      | sK3 != X1
% 3.01/1.02      | sK4 != X2
% 3.01/1.02      | sK5 != X0
% 3.01/1.02      | k1_xboole_0 = X2 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_36]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_676,plain,
% 3.01/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.01/1.02      | k1_relset_1(sK3,sK4,sK5) = sK3
% 3.01/1.02      | k1_xboole_0 = sK4 ),
% 3.01/1.02      inference(unflattening,[status(thm)],[c_675]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_678,plain,
% 3.01/1.02      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_676,c_35]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_17,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1369,plain,
% 3.01/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.01/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2571,plain,
% 3.01/1.02      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1363,c_1369]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2598,plain,
% 3.01/1.02      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_678,c_2571]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_30,plain,
% 3.01/1.02      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | ~ v1_relat_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_32,negated_conjecture,
% 3.01/1.02      ( ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
% 3.01/1.02      | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.01/1.02      | ~ v1_funct_1(k2_funct_1(sK5)) ),
% 3.01/1.02      inference(cnf_transformation,[],[f89]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_699,plain,
% 3.01/1.02      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.01/1.02      | ~ v1_relat_1(X0)
% 3.01/1.02      | k2_funct_1(sK5) != X0
% 3.01/1.02      | k1_relat_1(X0) != sK4
% 3.01/1.02      | k2_relat_1(X0) != sK3 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_30,c_32]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_700,plain,
% 3.01/1.02      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.01/1.02      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.01/1.02      | ~ v1_relat_1(k2_funct_1(sK5))
% 3.01/1.02      | k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.01/1.02      | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
% 3.01/1.02      inference(unflattening,[status(thm)],[c_699]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_712,plain,
% 3.01/1.02      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.01/1.02      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.01/1.02      | k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.01/1.02      | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
% 3.01/1.02      inference(forward_subsumption_resolution,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_700,c_15]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1348,plain,
% 3.01/1.02      ( k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.01/1.02      | k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_37,negated_conjecture,
% 3.01/1.02      ( v1_funct_1(sK5) ),
% 3.01/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_38,plain,
% 3.01/1.02      ( v1_funct_1(sK5) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_701,plain,
% 3.01/1.02      ( k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.01/1.02      | k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK5)) != iProver_top
% 3.01/1.02      | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_700]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_9,plain,
% 3.01/1.02      ( ~ v1_funct_1(X0)
% 3.01/1.02      | v1_funct_1(k2_funct_1(X0))
% 3.01/1.02      | ~ v1_relat_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1655,plain,
% 3.01/1.02      ( v1_funct_1(k2_funct_1(sK5))
% 3.01/1.02      | ~ v1_funct_1(sK5)
% 3.01/1.02      | ~ v1_relat_1(sK5) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1656,plain,
% 3.01/1.02      ( v1_funct_1(k2_funct_1(sK5)) = iProver_top
% 3.01/1.02      | v1_funct_1(sK5) != iProver_top
% 3.01/1.02      | v1_relat_1(sK5) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_1655]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_10,plain,
% 3.01/1.02      ( ~ v1_funct_1(X0)
% 3.01/1.02      | ~ v1_relat_1(X0)
% 3.01/1.02      | v1_relat_1(k2_funct_1(X0)) ),
% 3.01/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1668,plain,
% 3.01/1.02      ( ~ v1_funct_1(sK5)
% 3.01/1.02      | v1_relat_1(k2_funct_1(sK5))
% 3.01/1.02      | ~ v1_relat_1(sK5) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1669,plain,
% 3.01/1.02      ( v1_funct_1(sK5) != iProver_top
% 3.01/1.02      | v1_relat_1(k2_funct_1(sK5)) = iProver_top
% 3.01/1.02      | v1_relat_1(sK5) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_1668]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1969,plain,
% 3.01/1.02      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.01/1.02      | k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.01/1.02      | k1_relat_1(k2_funct_1(sK5)) != sK4 ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_1348,c_38,c_40,c_701,c_1656,c_1669,c_1680]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1970,plain,
% 3.01/1.02      ( k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.01/1.02      | k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.01/1.02      inference(renaming,[status(thm)],[c_1969]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_13,plain,
% 3.01/1.02      ( ~ v2_funct_1(X0)
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | ~ v1_relat_1(X0)
% 3.01/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_34,negated_conjecture,
% 3.01/1.02      ( v2_funct_1(sK5) ),
% 3.01/1.02      inference(cnf_transformation,[],[f87]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_413,plain,
% 3.01/1.02      ( ~ v1_funct_1(X0)
% 3.01/1.02      | ~ v1_relat_1(X0)
% 3.01/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.01/1.02      | sK5 != X0 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_34]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_414,plain,
% 3.01/1.02      ( ~ v1_funct_1(sK5)
% 3.01/1.02      | ~ v1_relat_1(sK5)
% 3.01/1.02      | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
% 3.01/1.02      inference(unflattening,[status(thm)],[c_413]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_416,plain,
% 3.01/1.02      ( ~ v1_relat_1(sK5)
% 3.01/1.02      | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_414,c_37]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1360,plain,
% 3.01/1.02      ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5)
% 3.01/1.02      | v1_relat_1(sK5) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1684,plain,
% 3.01/1.02      ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_1360,c_37,c_35,c_414,c_1679]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_14,plain,
% 3.01/1.02      ( ~ v2_funct_1(X0)
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | ~ v1_relat_1(X0)
% 3.01/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_399,plain,
% 3.01/1.02      ( ~ v1_funct_1(X0)
% 3.01/1.02      | ~ v1_relat_1(X0)
% 3.01/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.01/1.02      | sK5 != X0 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_34]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_400,plain,
% 3.01/1.02      ( ~ v1_funct_1(sK5)
% 3.01/1.02      | ~ v1_relat_1(sK5)
% 3.01/1.02      | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
% 3.01/1.02      inference(unflattening,[status(thm)],[c_399]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_402,plain,
% 3.01/1.02      ( ~ v1_relat_1(sK5)
% 3.01/1.02      | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_400,c_37]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1361,plain,
% 3.01/1.02      ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5)
% 3.01/1.02      | v1_relat_1(sK5) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1688,plain,
% 3.01/1.02      ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_1361,c_37,c_35,c_400,c_1679]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1973,plain,
% 3.01/1.02      ( k1_relat_1(sK5) != sK3
% 3.01/1.02      | k2_relat_1(sK5) != sK4
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_1970,c_1684,c_1688]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2546,plain,
% 3.01/1.02      ( k1_relat_1(sK5) != sK3
% 3.01/1.02      | sK4 != sK4
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_2522,c_1973]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2550,plain,
% 3.01/1.02      ( k1_relat_1(sK5) != sK3
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.01/1.02      inference(equality_resolution_simp,[status(thm)],[c_2546]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2796,plain,
% 3.01/1.02      ( sK4 = k1_xboole_0
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_2598,c_2550]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_29,plain,
% 3.01/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | ~ v1_relat_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1364,plain,
% 3.01/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.01/1.02      | v1_funct_1(X0) != iProver_top
% 3.01/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3147,plain,
% 3.01/1.02      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK5)),k1_relat_1(sK5)))) = iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK5)) != iProver_top
% 3.01/1.02      | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1684,c_1364]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2547,plain,
% 3.01/1.02      ( k1_relat_1(k2_funct_1(sK5)) = sK4 ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_2522,c_1688]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3184,plain,
% 3.01/1.02      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k1_relat_1(sK5)))) = iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK5)) != iProver_top
% 3.01/1.02      | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_3147,c_2547]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3858,plain,
% 3.01/1.02      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k1_relat_1(sK5)))) = iProver_top ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_3184,c_38,c_40,c_1656,c_1669,c_1680]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3863,plain,
% 3.01/1.02      ( sK4 = k1_xboole_0
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_2598,c_3858]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4070,plain,
% 3.01/1.02      ( v1_xboole_0(sK5) = iProver_top ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_3900,c_40,c_123,c_1680,c_2280,c_2564,c_2796,c_3863]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1,plain,
% 3.01/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.01/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3,plain,
% 3.01/1.02      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.01/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_448,plain,
% 3.01/1.02      ( ~ v1_xboole_0(X0) | X1 != X0 | sK1(X1) != X2 | k1_xboole_0 = X1 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_3]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_449,plain,
% 3.01/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.01/1.02      inference(unflattening,[status(thm)],[c_448]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1358,plain,
% 3.01/1.02      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4075,plain,
% 3.01/1.02      ( sK5 = k1_xboole_0 ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_4070,c_1358]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_22,plain,
% 3.01/1.02      ( v1_funct_2(X0,X1,X2)
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | k1_relset_1(X1,X2,X0) != X1
% 3.01/1.02      | k1_xboole_0 = X2 ),
% 3.01/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_659,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.01/1.02      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.01/1.02      | k1_relset_1(X1,X2,X0) != X1
% 3.01/1.02      | k2_funct_1(sK5) != X0
% 3.01/1.02      | sK3 != X2
% 3.01/1.02      | sK4 != X1
% 3.01/1.02      | k1_xboole_0 = X2 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_660,plain,
% 3.01/1.02      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.01/1.02      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.01/1.02      | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != sK4
% 3.01/1.02      | k1_xboole_0 = sK3 ),
% 3.01/1.02      inference(unflattening,[status(thm)],[c_659]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1350,plain,
% 3.01/1.02      ( k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != sK4
% 3.01/1.02      | k1_xboole_0 = sK3
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_661,plain,
% 3.01/1.02      ( k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != sK4
% 3.01/1.02      | k1_xboole_0 = sK3
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1850,plain,
% 3.01/1.02      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.01/1.02      | k1_xboole_0 = sK3
% 3.01/1.02      | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != sK4 ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_1350,c_38,c_40,c_661,c_1656,c_1680]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1851,plain,
% 3.01/1.02      ( k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != sK4
% 3.01/1.02      | k1_xboole_0 = sK3
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.01/1.02      inference(renaming,[status(thm)],[c_1850]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4098,plain,
% 3.01/1.02      ( k1_relset_1(sK4,sK3,k2_funct_1(k1_xboole_0)) != sK4
% 3.01/1.02      | sK3 = k1_xboole_0
% 3.01/1.02      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_4075,c_1851]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_451,plain,
% 3.01/1.02      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_449]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_718,plain,
% 3.01/1.02      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.01/1.02      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.01/1.02      | k2_funct_1(sK5) != sK5
% 3.01/1.02      | sK3 != sK4 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_32,c_36]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1347,plain,
% 3.01/1.02      ( k2_funct_1(sK5) != sK5
% 3.01/1.02      | sK3 != sK4
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_719,plain,
% 3.01/1.02      ( k2_funct_1(sK5) != sK5
% 3.01/1.02      | sK3 != sK4
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1799,plain,
% 3.01/1.02      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.01/1.02      | sK3 != sK4
% 3.01/1.02      | k2_funct_1(sK5) != sK5 ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_1347,c_38,c_40,c_719,c_1656,c_1680]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1800,plain,
% 3.01/1.02      ( k2_funct_1(sK5) != sK5
% 3.01/1.02      | sK3 != sK4
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.01/1.02      inference(renaming,[status(thm)],[c_1799]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_792,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1839,plain,
% 3.01/1.02      ( sK3 != X0 | sK3 = sK4 | sK4 != X0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_792]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1840,plain,
% 3.01/1.02      ( sK3 = sK4 | sK3 != k1_xboole_0 | sK4 != k1_xboole_0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_1839]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1862,plain,
% 3.01/1.02      ( ~ v1_xboole_0(sK5) | k1_xboole_0 = sK5 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_449]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1865,plain,
% 3.01/1.02      ( k1_xboole_0 = sK5 | v1_xboole_0(sK5) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_1862]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_791,plain,( X0 = X0 ),theory(equality) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1891,plain,
% 3.01/1.02      ( sK5 = sK5 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_791]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1846,plain,
% 3.01/1.02      ( k1_relat_1(sK5) != X0
% 3.01/1.02      | k1_relat_1(sK5) = k1_xboole_0
% 3.01/1.02      | k1_xboole_0 != X0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_792]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1996,plain,
% 3.01/1.02      ( k1_relat_1(sK5) != k1_relat_1(X0)
% 3.01/1.02      | k1_relat_1(sK5) = k1_xboole_0
% 3.01/1.02      | k1_xboole_0 != k1_relat_1(X0) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_1846]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1998,plain,
% 3.01/1.02      ( k1_relat_1(sK5) != k1_relat_1(k1_xboole_0)
% 3.01/1.02      | k1_relat_1(sK5) = k1_xboole_0
% 3.01/1.02      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_1996]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_798,plain,
% 3.01/1.02      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 3.01/1.02      theory(equality) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1997,plain,
% 3.01/1.02      ( k1_relat_1(sK5) = k1_relat_1(X0) | sK5 != X0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_798]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1999,plain,
% 3.01/1.02      ( k1_relat_1(sK5) = k1_relat_1(k1_xboole_0) | sK5 != k1_xboole_0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_1997]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2647,plain,
% 3.01/1.02      ( k1_relat_1(X0) != X1
% 3.01/1.02      | k1_xboole_0 != X1
% 3.01/1.02      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_792]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2648,plain,
% 3.01/1.02      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 3.01/1.02      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 3.01/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_2647]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2797,plain,
% 3.01/1.02      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.01/1.02      | sK4 = k1_xboole_0 ),
% 3.01/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2796]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2347,plain,
% 3.01/1.02      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_792]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2964,plain,
% 3.01/1.02      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_2347]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2965,plain,
% 3.01/1.02      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_2964]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_795,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.01/1.02      theory(equality) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1783,plain,
% 3.01/1.02      ( m1_subset_1(X0,X1)
% 3.01/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
% 3.01/1.02      | X1 != k1_zfmisc_1(X2)
% 3.01/1.02      | X0 != k1_xboole_0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_795]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2182,plain,
% 3.01/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.01/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
% 3.01/1.02      | X0 != k1_xboole_0
% 3.01/1.02      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_1783]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3216,plain,
% 3.01/1.02      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.01/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.01/1.02      | k2_funct_1(sK5) != k1_xboole_0
% 3.01/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_2182]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3217,plain,
% 3.01/1.02      ( k2_funct_1(sK5) != k1_xboole_0
% 3.01/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top
% 3.01/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_3216]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4,plain,
% 3.01/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.01/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1672,plain,
% 3.01/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3615,plain,
% 3.01/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_1672]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3616,plain,
% 3.01/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_3615]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3650,plain,
% 3.01/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_1672]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3651,plain,
% 3.01/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_3650]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2513,plain,
% 3.01/1.02      ( k2_funct_1(sK5) = k1_xboole_0
% 3.01/1.02      | k1_relat_1(sK5) != k1_xboole_0
% 3.01/1.02      | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1684,c_1377]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2514,plain,
% 3.01/1.02      ( ~ v1_relat_1(k2_funct_1(sK5))
% 3.01/1.02      | k2_funct_1(sK5) = k1_xboole_0
% 3.01/1.02      | k1_relat_1(sK5) != k1_xboole_0 ),
% 3.01/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2513]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3692,plain,
% 3.01/1.02      ( k1_relat_1(sK5) != k1_xboole_0 | k2_funct_1(sK5) = k1_xboole_0 ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_2513,c_37,c_35,c_1668,c_1679,c_2514]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3693,plain,
% 3.01/1.02      ( k2_funct_1(sK5) = k1_xboole_0 | k1_relat_1(sK5) != k1_xboole_0 ),
% 3.01/1.02      inference(renaming,[status(thm)],[c_3692]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1877,plain,
% 3.01/1.02      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_792]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4377,plain,
% 3.01/1.02      ( k2_funct_1(sK5) != X0 | k2_funct_1(sK5) = sK5 | sK5 != X0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_1877]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4378,plain,
% 3.01/1.02      ( k2_funct_1(sK5) = sK5
% 3.01/1.02      | k2_funct_1(sK5) != k1_xboole_0
% 3.01/1.02      | sK5 != k1_xboole_0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_4377]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2183,plain,
% 3.01/1.02      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_791]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3472,plain,
% 3.01/1.02      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_2183]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4741,plain,
% 3.01/1.02      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_3472]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_7,plain,
% 3.01/1.02      ( ~ v1_relat_1(X0)
% 3.01/1.02      | k1_relat_1(X0) != k1_xboole_0
% 3.01/1.02      | k1_xboole_0 = X0 ),
% 3.01/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1376,plain,
% 3.01/1.02      ( k1_relat_1(X0) != k1_xboole_0
% 3.01/1.02      | k1_xboole_0 = X0
% 3.01/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2382,plain,
% 3.01/1.02      ( k2_funct_1(sK5) = k1_xboole_0
% 3.01/1.02      | k2_relat_1(sK5) != k1_xboole_0
% 3.01/1.02      | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1688,c_1376]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2383,plain,
% 3.01/1.02      ( ~ v1_relat_1(k2_funct_1(sK5))
% 3.01/1.02      | k2_funct_1(sK5) = k1_xboole_0
% 3.01/1.02      | k2_relat_1(sK5) != k1_xboole_0 ),
% 3.01/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2382]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2439,plain,
% 3.01/1.02      ( k2_relat_1(sK5) != k1_xboole_0 | k2_funct_1(sK5) = k1_xboole_0 ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_2382,c_37,c_35,c_1668,c_1679,c_2383]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2440,plain,
% 3.01/1.02      ( k2_funct_1(sK5) = k1_xboole_0 | k2_relat_1(sK5) != k1_xboole_0 ),
% 3.01/1.02      inference(renaming,[status(thm)],[c_2439]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2544,plain,
% 3.01/1.02      ( k2_funct_1(sK5) = k1_xboole_0 | sK4 != k1_xboole_0 ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_2522,c_2440]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4090,plain,
% 3.01/1.02      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 | sK4 != k1_xboole_0 ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_4075,c_2544]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4834,plain,
% 3.01/1.02      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_4090,c_2796,c_3863]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_23,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.01/1.02      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.01/1.02      inference(cnf_transformation,[],[f94]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_569,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.01/1.02      | ~ v1_funct_1(X2)
% 3.01/1.02      | ~ v1_relat_1(X2)
% 3.01/1.02      | X2 != X0
% 3.01/1.02      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.01/1.02      | k1_relat_1(X2) != k1_xboole_0
% 3.01/1.02      | k2_relat_1(X2) != X1 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_570,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | ~ v1_relat_1(X0)
% 3.01/1.02      | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 3.01/1.02      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.01/1.02      inference(unflattening,[status(thm)],[c_569]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_584,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 3.01/1.02      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.01/1.02      inference(forward_subsumption_resolution,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_570,c_15]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1354,plain,
% 3.01/1.02      ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 3.01/1.02      | k1_relat_1(X0) != k1_xboole_0
% 3.01/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0)))) != iProver_top
% 3.01/1.02      | v1_funct_1(X0) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_584]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2448,plain,
% 3.01/1.02      ( k1_relset_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK5)),k2_funct_1(sK5)) = k1_xboole_0
% 3.01/1.02      | k2_relat_1(sK5) != k1_xboole_0
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK5))))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1688,c_1354]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2449,plain,
% 3.01/1.02      ( k1_relset_1(k1_xboole_0,k1_relat_1(sK5),k2_funct_1(sK5)) = k1_xboole_0
% 3.01/1.02      | k2_relat_1(sK5) != k1_xboole_0
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK5)))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_2448,c_1684]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2585,plain,
% 3.01/1.02      ( k1_relset_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK5)),k2_funct_1(sK5)) = k1_xboole_0
% 3.01/1.02      | sK4 != k1_xboole_0
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK5))))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_2547,c_1354]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2591,plain,
% 3.01/1.02      ( k1_relset_1(k1_xboole_0,k1_relat_1(sK5),k2_funct_1(sK5)) = k1_xboole_0
% 3.01/1.02      | sK4 != k1_xboole_0
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK5)))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_2585,c_1684]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4525,plain,
% 3.01/1.02      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK5)))) != iProver_top
% 3.01/1.02      | k1_relset_1(k1_xboole_0,k1_relat_1(sK5),k2_funct_1(sK5)) = k1_xboole_0 ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_2449,c_38,c_40,c_1656,c_1680,c_2591,c_2796,c_3863]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4526,plain,
% 3.01/1.02      ( k1_relset_1(k1_xboole_0,k1_relat_1(sK5),k2_funct_1(sK5)) = k1_xboole_0
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK5)))) != iProver_top ),
% 3.01/1.02      inference(renaming,[status(thm)],[c_4525]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4529,plain,
% 3.01/1.02      ( k1_relset_1(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 3.01/1.02      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) != iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_4526,c_4075]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4840,plain,
% 3.01/1.02      ( k1_relset_1(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0
% 3.01/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) != iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_4834,c_4529]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4092,plain,
% 3.01/1.02      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = sK4 ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_4075,c_2547]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4842,plain,
% 3.01/1.02      ( k1_relat_1(k1_xboole_0) = sK4 ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_4834,c_4092]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4847,plain,
% 3.01/1.02      ( k1_relset_1(k1_xboole_0,sK4,k1_xboole_0) = k1_xboole_0
% 3.01/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_4840,c_4842]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1378,plain,
% 3.01/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2569,plain,
% 3.01/1.02      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1378,c_1369]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4850,plain,
% 3.01/1.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 3.01/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_4847,c_2569]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4956,plain,
% 3.01/1.02      ( k1_relset_1(sK4,sK3,k2_funct_1(k1_xboole_0)) != sK4
% 3.01/1.02      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_4098,c_37,c_35,c_40,c_718,c_1655,c_1679,c_1680,c_1840,
% 3.01/1.02                 c_2544,c_2564,c_2796,c_3216,c_3615,c_3863,c_4378,c_4741]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4960,plain,
% 3.01/1.02      ( k1_relset_1(sK4,sK3,k1_xboole_0) != sK4
% 3.01/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_4956,c_4834]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4961,plain,
% 3.01/1.02      ( k1_relat_1(k1_xboole_0) != sK4
% 3.01/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_4960,c_2569]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4964,plain,
% 3.01/1.02      ( k1_relat_1(k1_xboole_0) != sK4 ),
% 3.01/1.02      inference(forward_subsumption_resolution,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_4961,c_1378]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(contradiction,plain,
% 3.01/1.02      ( $false ),
% 3.01/1.02      inference(minisat,[status(thm)],[c_4964,c_4842]) ).
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
% 3.01/1.02  parsing_time:                           0.01
% 3.01/1.02  unif_index_cands_time:                  0.
% 3.01/1.02  unif_index_add_time:                    0.
% 3.01/1.02  orderings_time:                         0.
% 3.01/1.02  out_proof_time:                         0.012
% 3.01/1.02  total_time:                             0.17
% 3.01/1.02  num_of_symbols:                         53
% 3.01/1.02  num_of_terms:                           3702
% 3.01/1.02  
% 3.01/1.02  ------ Preprocessing
% 3.01/1.02  
% 3.01/1.02  num_of_splits:                          0
% 3.01/1.02  num_of_split_atoms:                     0
% 3.01/1.02  num_of_reused_defs:                     0
% 3.01/1.02  num_eq_ax_congr_red:                    9
% 3.01/1.02  num_of_sem_filtered_clauses:            1
% 3.01/1.02  num_of_subtypes:                        0
% 3.01/1.02  monotx_restored_types:                  0
% 3.01/1.02  sat_num_of_epr_types:                   0
% 3.01/1.02  sat_num_of_non_cyclic_types:            0
% 3.01/1.02  sat_guarded_non_collapsed_types:        0
% 3.01/1.02  num_pure_diseq_elim:                    0
% 3.01/1.02  simp_replaced_by:                       0
% 3.01/1.02  res_preprocessed:                       146
% 3.01/1.02  prep_upred:                             0
% 3.01/1.02  prep_unflattend:                        62
% 3.01/1.02  smt_new_axioms:                         0
% 3.01/1.02  pred_elim_cands:                        7
% 3.01/1.02  pred_elim:                              3
% 3.01/1.02  pred_elim_cl:                           -2
% 3.01/1.02  pred_elim_cycles:                       4
% 3.01/1.02  merged_defs:                            0
% 3.01/1.02  merged_defs_ncl:                        0
% 3.01/1.02  bin_hyper_res:                          0
% 3.01/1.02  prep_cycles:                            3
% 3.01/1.02  pred_elim_time:                         0.009
% 3.01/1.02  splitting_time:                         0.
% 3.01/1.02  sem_filter_time:                        0.
% 3.01/1.02  monotx_time:                            0.
% 3.01/1.02  subtype_inf_time:                       0.
% 3.01/1.02  
% 3.01/1.02  ------ Problem properties
% 3.01/1.02  
% 3.01/1.02  clauses:                                39
% 3.01/1.02  conjectures:                            3
% 3.01/1.02  epr:                                    3
% 3.01/1.02  horn:                                   32
% 3.01/1.02  ground:                                 16
% 3.01/1.02  unary:                                  12
% 3.01/1.02  binary:                                 9
% 3.01/1.02  lits:                                   94
% 3.01/1.02  lits_eq:                                40
% 3.01/1.02  fd_pure:                                0
% 3.01/1.02  fd_pseudo:                              0
% 3.01/1.02  fd_cond:                                5
% 3.01/1.02  fd_pseudo_cond:                         0
% 3.01/1.02  ac_symbols:                             0
% 3.01/1.02  
% 3.01/1.02  ------ Propositional Solver
% 3.01/1.02  
% 3.01/1.02  prop_solver_calls:                      23
% 3.01/1.02  prop_fast_solver_calls:                 1004
% 3.01/1.02  smt_solver_calls:                       0
% 3.01/1.02  smt_fast_solver_calls:                  0
% 3.01/1.02  prop_num_of_clauses:                    1718
% 3.01/1.02  prop_preprocess_simplified:             5845
% 3.01/1.02  prop_fo_subsumed:                       28
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
% 3.01/1.02  inst_num_of_clauses:                    644
% 3.01/1.02  inst_num_in_passive:                    128
% 3.01/1.02  inst_num_in_active:                     319
% 3.01/1.02  inst_num_in_unprocessed:                198
% 3.01/1.02  inst_num_of_loops:                      410
% 3.01/1.02  inst_num_of_learning_restarts:          0
% 3.01/1.02  inst_num_moves_active_passive:          89
% 3.01/1.02  inst_lit_activity:                      0
% 3.01/1.02  inst_lit_activity_moves:                0
% 3.01/1.02  inst_num_tautologies:                   0
% 3.01/1.02  inst_num_prop_implied:                  0
% 3.01/1.02  inst_num_existing_simplified:           0
% 3.01/1.02  inst_num_eq_res_simplified:             0
% 3.01/1.02  inst_num_child_elim:                    0
% 3.01/1.02  inst_num_of_dismatching_blockings:      151
% 3.01/1.02  inst_num_of_non_proper_insts:           373
% 3.01/1.02  inst_num_of_duplicates:                 0
% 3.01/1.02  inst_inst_num_from_inst_to_res:         0
% 3.01/1.02  inst_dismatching_checking_time:         0.
% 3.01/1.02  
% 3.01/1.02  ------ Resolution
% 3.01/1.02  
% 3.01/1.02  res_num_of_clauses:                     0
% 3.01/1.02  res_num_in_passive:                     0
% 3.01/1.02  res_num_in_active:                      0
% 3.01/1.02  res_num_of_loops:                       149
% 3.01/1.02  res_forward_subset_subsumed:            33
% 3.01/1.02  res_backward_subset_subsumed:           2
% 3.01/1.02  res_forward_subsumed:                   0
% 3.01/1.02  res_backward_subsumed:                  0
% 3.01/1.02  res_forward_subsumption_resolution:     5
% 3.01/1.02  res_backward_subsumption_resolution:    0
% 3.01/1.02  res_clause_to_clause_subsumption:       162
% 3.01/1.02  res_orphan_elimination:                 0
% 3.01/1.02  res_tautology_del:                      89
% 3.01/1.02  res_num_eq_res_simplified:              0
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
% 3.01/1.02  sup_num_of_clauses:                     77
% 3.01/1.02  sup_num_in_active:                      38
% 3.01/1.02  sup_num_in_passive:                     39
% 3.01/1.02  sup_num_of_loops:                       81
% 3.01/1.02  sup_fw_superposition:                   50
% 3.01/1.02  sup_bw_superposition:                   43
% 3.01/1.02  sup_immediate_simplified:               46
% 3.01/1.02  sup_given_eliminated:                   0
% 3.01/1.02  comparisons_done:                       0
% 3.01/1.02  comparisons_avoided:                    13
% 3.01/1.02  
% 3.01/1.02  ------ Simplifications
% 3.01/1.02  
% 3.01/1.02  
% 3.01/1.02  sim_fw_subset_subsumed:                 16
% 3.01/1.02  sim_bw_subset_subsumed:                 5
% 3.01/1.02  sim_fw_subsumed:                        11
% 3.01/1.02  sim_bw_subsumed:                        1
% 3.01/1.02  sim_fw_subsumption_res:                 2
% 3.01/1.02  sim_bw_subsumption_res:                 1
% 3.01/1.02  sim_tautology_del:                      3
% 3.01/1.02  sim_eq_tautology_del:                   7
% 3.01/1.02  sim_eq_res_simp:                        1
% 3.01/1.02  sim_fw_demodulated:                     6
% 3.01/1.02  sim_bw_demodulated:                     41
% 3.01/1.02  sim_light_normalised:                   22
% 3.01/1.02  sim_joinable_taut:                      0
% 3.01/1.02  sim_joinable_simp:                      0
% 3.01/1.02  sim_ac_normalised:                      0
% 3.01/1.02  sim_smt_subsumption:                    0
% 3.01/1.02  
%------------------------------------------------------------------------------
