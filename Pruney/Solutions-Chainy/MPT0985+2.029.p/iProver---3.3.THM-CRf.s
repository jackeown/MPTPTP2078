%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:25 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  189 (2764 expanded)
%              Number of clauses        :  124 ( 872 expanded)
%              Number of leaves         :   20 ( 548 expanded)
%              Depth                    :   22
%              Number of atoms          :  581 (15051 expanded)
%              Number of equality atoms :  281 (3007 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(nnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
        | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
        | ~ v1_funct_1(k2_funct_1(sK4)) )
      & k2_relset_1(sK2,sK3,sK4) = sK3
      & v2_funct_1(sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
      | ~ v1_funct_1(k2_funct_1(sK4)) )
    & k2_relset_1(sK2,sK3,sK4) = sK3
    & v2_funct_1(sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f43])).

fof(f73,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f70,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f77,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f57,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f59,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f58,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_1192,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3229,plain,
    ( X0 != X1
    | k2_relat_1(X2) != X1
    | k2_relat_1(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_1192])).

cnf(c_6183,plain,
    ( k2_relat_1(k2_funct_1(sK4)) != X0
    | k2_relat_1(k2_funct_1(sK4)) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_3229])).

cnf(c_6184,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = sK2
    | k2_relat_1(k2_funct_1(sK4)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6183])).

cnf(c_2947,plain,
    ( k1_relset_1(sK3,sK2,k2_funct_1(sK4)) != X0
    | k1_relset_1(sK3,sK2,k2_funct_1(sK4)) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1192])).

cnf(c_4644,plain,
    ( k1_relset_1(sK3,sK2,k2_funct_1(sK4)) != k1_relat_1(k2_funct_1(sK4))
    | k1_relset_1(sK3,sK2,k2_funct_1(sK4)) = sK3
    | sK3 != k1_relat_1(k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_2947])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1920,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_719,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_720,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_719])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_722,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_720,c_30])).

cnf(c_1909,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1912,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3469,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1909,c_1912])).

cnf(c_3679,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_722,c_3469])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1911,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3042,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1909,c_1911])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3044,plain,
    ( k2_relat_1(sK4) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3042,c_28])).

cnf(c_25,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_27,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_730,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK4) != X0
    | k1_relat_1(X0) != sK3
    | k2_relat_1(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_27])).

cnf(c_731,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_743,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_731,c_15])).

cnf(c_1898,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_33,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_732,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_2179,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2180,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2179])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2225,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2226,plain,
    ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2225])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2224,plain,
    ( ~ v1_funct_1(sK4)
    | v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2228,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2224])).

cnf(c_2239,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1898,c_33,c_35,c_732,c_2180,c_2226,c_2228])).

cnf(c_2240,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2239])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_29,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_476,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_477,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_479,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_477,c_32])).

cnf(c_1906,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_2188,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1906,c_32,c_30,c_477,c_2179])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_462,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_463,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_465,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_463,c_32])).

cnf(c_1907,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_2192,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1907,c_32,c_30,c_463,c_2179])).

cnf(c_2243,plain,
    ( k1_relat_1(sK4) != sK2
    | k2_relat_1(sK4) != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2240,c_2188,c_2192])).

cnf(c_3099,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3044,c_2243])).

cnf(c_3103,plain,
    ( k1_relat_1(sK4) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3099])).

cnf(c_3817,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3679,c_3103])).

cnf(c_3981,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1920,c_3817])).

cnf(c_24,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1910,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3423,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2188,c_1910])).

cnf(c_3100,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
    inference(demodulation,[status(thm)],[c_3044,c_2192])).

cnf(c_3442,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3423,c_3100])).

cnf(c_4057,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3442,c_33,c_35,c_2180,c_2226,c_2228])).

cnf(c_4062,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3679,c_4057])).

cnf(c_4323,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3981,c_3817,c_4062])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1918,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3111,plain,
    ( sK3 != k1_xboole_0
    | sK4 = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3044,c_1918])).

cnf(c_3112,plain,
    ( ~ v1_relat_1(sK4)
    | sK3 != k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3111])).

cnf(c_3181,plain,
    ( sK4 = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3111,c_30,c_2179,c_3112])).

cnf(c_3182,plain,
    ( sK3 != k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3181])).

cnf(c_4336,plain,
    ( sK4 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4323,c_3182])).

cnf(c_4394,plain,
    ( sK4 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4336])).

cnf(c_4339,plain,
    ( k2_relat_1(sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4323,c_3044])).

cnf(c_4398,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4394,c_4339])).

cnf(c_1197,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_4038,plain,
    ( k2_funct_1(sK4) != X0
    | k2_relat_1(k2_funct_1(sK4)) = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1197])).

cnf(c_4040,plain,
    ( k2_funct_1(sK4) != k1_xboole_0
    | k2_relat_1(k2_funct_1(sK4)) = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4038])).

cnf(c_3156,plain,
    ( k2_relat_1(k2_funct_1(sK4)) != X0
    | k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1192])).

cnf(c_4037,plain,
    ( k2_relat_1(k2_funct_1(sK4)) != k2_relat_1(X0)
    | k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_3156])).

cnf(c_4039,plain,
    ( k2_relat_1(k2_funct_1(sK4)) != k2_relat_1(k1_xboole_0)
    | k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4037])).

cnf(c_2866,plain,
    ( X0 != X1
    | X0 = k1_relat_1(X2)
    | k1_relat_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1192])).

cnf(c_3406,plain,
    ( X0 = k1_relat_1(k2_funct_1(sK4))
    | X0 != k2_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2866])).

cnf(c_3918,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
    | sK3 = k1_relat_1(k2_funct_1(sK4))
    | sK3 != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_3406])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3133,plain,
    ( ~ r2_hidden(sK1(X0,k2_zfmisc_1(X1,X2)),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3710,plain,
    ( ~ r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4))
    | ~ v1_xboole_0(k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_3133])).

cnf(c_3512,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | k1_relset_1(sK3,sK2,k2_funct_1(sK4)) = k1_relat_1(k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1917,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3114,plain,
    ( k2_funct_1(sK4) = k1_xboole_0
    | sK3 != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3100,c_1917])).

cnf(c_2310,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1192])).

cnf(c_2632,plain,
    ( k2_relat_1(sK4) != X0
    | sK3 != X0
    | sK3 = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2310])).

cnf(c_3029,plain,
    ( k2_relat_1(sK4) != sK3
    | sK3 = k2_relat_1(sK4)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2632])).

cnf(c_2687,plain,
    ( k2_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1192])).

cnf(c_2688,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2687])).

cnf(c_2315,plain,
    ( X0 != X1
    | k1_relat_1(X2) != X1
    | k1_relat_1(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_1192])).

cnf(c_2546,plain,
    ( X0 != k2_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = X0
    | k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2315])).

cnf(c_2631,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = sK3
    | sK3 != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2546])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2258,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK1(X0,k2_zfmisc_1(X1,X2)),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2574,plain,
    ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2))
    | r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_2258])).

cnf(c_2174,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2502,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_2174])).

cnf(c_1191,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2309,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1191])).

cnf(c_2306,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1191])).

cnf(c_2196,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1192])).

cnf(c_2305,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2196])).

cnf(c_1193,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2253,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_funct_1(sK4))
    | k2_funct_1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1193])).

cnf(c_2255,plain,
    ( v1_xboole_0(k2_funct_1(sK4))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_funct_1(sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2253])).

cnf(c_1218,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1191])).

cnf(c_21,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_703,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK4) != X0
    | sK2 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_704,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relset_1(sK3,sK2,k2_funct_1(sK4)) != sK3
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_703])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6184,c_4644,c_4398,c_4323,c_4040,c_4039,c_3918,c_3710,c_3512,c_3114,c_3044,c_3029,c_2688,c_2631,c_2574,c_2502,c_2309,c_2306,c_2305,c_2255,c_2228,c_2224,c_2225,c_2180,c_2179,c_1218,c_731,c_704,c_463,c_5,c_35,c_30,c_33,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.23/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.23/1.00  
% 3.23/1.00  ------  iProver source info
% 3.23/1.00  
% 3.23/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.23/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.23/1.00  git: non_committed_changes: false
% 3.23/1.00  git: last_make_outside_of_git: false
% 3.23/1.00  
% 3.23/1.00  ------ 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options
% 3.23/1.00  
% 3.23/1.00  --out_options                           all
% 3.23/1.00  --tptp_safe_out                         true
% 3.23/1.00  --problem_path                          ""
% 3.23/1.00  --include_path                          ""
% 3.23/1.00  --clausifier                            res/vclausify_rel
% 3.23/1.00  --clausifier_options                    --mode clausify
% 3.23/1.00  --stdin                                 false
% 3.23/1.00  --stats_out                             all
% 3.23/1.00  
% 3.23/1.00  ------ General Options
% 3.23/1.00  
% 3.23/1.00  --fof                                   false
% 3.23/1.00  --time_out_real                         305.
% 3.23/1.00  --time_out_virtual                      -1.
% 3.23/1.00  --symbol_type_check                     false
% 3.23/1.00  --clausify_out                          false
% 3.23/1.00  --sig_cnt_out                           false
% 3.23/1.00  --trig_cnt_out                          false
% 3.23/1.00  --trig_cnt_out_tolerance                1.
% 3.23/1.00  --trig_cnt_out_sk_spl                   false
% 3.23/1.00  --abstr_cl_out                          false
% 3.23/1.00  
% 3.23/1.00  ------ Global Options
% 3.23/1.00  
% 3.23/1.00  --schedule                              default
% 3.23/1.00  --add_important_lit                     false
% 3.23/1.00  --prop_solver_per_cl                    1000
% 3.23/1.00  --min_unsat_core                        false
% 3.23/1.00  --soft_assumptions                      false
% 3.23/1.00  --soft_lemma_size                       3
% 3.23/1.00  --prop_impl_unit_size                   0
% 3.23/1.00  --prop_impl_unit                        []
% 3.23/1.00  --share_sel_clauses                     true
% 3.23/1.00  --reset_solvers                         false
% 3.23/1.00  --bc_imp_inh                            [conj_cone]
% 3.23/1.00  --conj_cone_tolerance                   3.
% 3.23/1.00  --extra_neg_conj                        none
% 3.23/1.00  --large_theory_mode                     true
% 3.23/1.00  --prolific_symb_bound                   200
% 3.23/1.00  --lt_threshold                          2000
% 3.23/1.00  --clause_weak_htbl                      true
% 3.23/1.00  --gc_record_bc_elim                     false
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing Options
% 3.23/1.00  
% 3.23/1.00  --preprocessing_flag                    true
% 3.23/1.00  --time_out_prep_mult                    0.1
% 3.23/1.00  --splitting_mode                        input
% 3.23/1.00  --splitting_grd                         true
% 3.23/1.00  --splitting_cvd                         false
% 3.23/1.00  --splitting_cvd_svl                     false
% 3.23/1.00  --splitting_nvd                         32
% 3.23/1.00  --sub_typing                            true
% 3.23/1.00  --prep_gs_sim                           true
% 3.23/1.00  --prep_unflatten                        true
% 3.23/1.00  --prep_res_sim                          true
% 3.23/1.00  --prep_upred                            true
% 3.23/1.00  --prep_sem_filter                       exhaustive
% 3.23/1.00  --prep_sem_filter_out                   false
% 3.23/1.00  --pred_elim                             true
% 3.23/1.00  --res_sim_input                         true
% 3.23/1.00  --eq_ax_congr_red                       true
% 3.23/1.00  --pure_diseq_elim                       true
% 3.23/1.00  --brand_transform                       false
% 3.23/1.00  --non_eq_to_eq                          false
% 3.23/1.00  --prep_def_merge                        true
% 3.23/1.00  --prep_def_merge_prop_impl              false
% 3.23/1.00  --prep_def_merge_mbd                    true
% 3.23/1.00  --prep_def_merge_tr_red                 false
% 3.23/1.00  --prep_def_merge_tr_cl                  false
% 3.23/1.00  --smt_preprocessing                     true
% 3.23/1.00  --smt_ac_axioms                         fast
% 3.23/1.00  --preprocessed_out                      false
% 3.23/1.00  --preprocessed_stats                    false
% 3.23/1.00  
% 3.23/1.00  ------ Abstraction refinement Options
% 3.23/1.00  
% 3.23/1.00  --abstr_ref                             []
% 3.23/1.00  --abstr_ref_prep                        false
% 3.23/1.00  --abstr_ref_until_sat                   false
% 3.23/1.00  --abstr_ref_sig_restrict                funpre
% 3.23/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/1.00  --abstr_ref_under                       []
% 3.23/1.00  
% 3.23/1.00  ------ SAT Options
% 3.23/1.00  
% 3.23/1.00  --sat_mode                              false
% 3.23/1.00  --sat_fm_restart_options                ""
% 3.23/1.00  --sat_gr_def                            false
% 3.23/1.00  --sat_epr_types                         true
% 3.23/1.00  --sat_non_cyclic_types                  false
% 3.23/1.00  --sat_finite_models                     false
% 3.23/1.00  --sat_fm_lemmas                         false
% 3.23/1.00  --sat_fm_prep                           false
% 3.23/1.00  --sat_fm_uc_incr                        true
% 3.23/1.00  --sat_out_model                         small
% 3.23/1.00  --sat_out_clauses                       false
% 3.23/1.00  
% 3.23/1.00  ------ QBF Options
% 3.23/1.00  
% 3.23/1.00  --qbf_mode                              false
% 3.23/1.00  --qbf_elim_univ                         false
% 3.23/1.00  --qbf_dom_inst                          none
% 3.23/1.00  --qbf_dom_pre_inst                      false
% 3.23/1.00  --qbf_sk_in                             false
% 3.23/1.00  --qbf_pred_elim                         true
% 3.23/1.00  --qbf_split                             512
% 3.23/1.00  
% 3.23/1.00  ------ BMC1 Options
% 3.23/1.00  
% 3.23/1.00  --bmc1_incremental                      false
% 3.23/1.00  --bmc1_axioms                           reachable_all
% 3.23/1.00  --bmc1_min_bound                        0
% 3.23/1.00  --bmc1_max_bound                        -1
% 3.23/1.00  --bmc1_max_bound_default                -1
% 3.23/1.00  --bmc1_symbol_reachability              true
% 3.23/1.00  --bmc1_property_lemmas                  false
% 3.23/1.00  --bmc1_k_induction                      false
% 3.23/1.00  --bmc1_non_equiv_states                 false
% 3.23/1.00  --bmc1_deadlock                         false
% 3.23/1.00  --bmc1_ucm                              false
% 3.23/1.00  --bmc1_add_unsat_core                   none
% 3.23/1.00  --bmc1_unsat_core_children              false
% 3.23/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/1.00  --bmc1_out_stat                         full
% 3.23/1.00  --bmc1_ground_init                      false
% 3.23/1.00  --bmc1_pre_inst_next_state              false
% 3.23/1.00  --bmc1_pre_inst_state                   false
% 3.23/1.00  --bmc1_pre_inst_reach_state             false
% 3.23/1.00  --bmc1_out_unsat_core                   false
% 3.23/1.00  --bmc1_aig_witness_out                  false
% 3.23/1.00  --bmc1_verbose                          false
% 3.23/1.00  --bmc1_dump_clauses_tptp                false
% 3.23/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.23/1.00  --bmc1_dump_file                        -
% 3.23/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.23/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.23/1.00  --bmc1_ucm_extend_mode                  1
% 3.23/1.00  --bmc1_ucm_init_mode                    2
% 3.23/1.00  --bmc1_ucm_cone_mode                    none
% 3.23/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.23/1.00  --bmc1_ucm_relax_model                  4
% 3.23/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.23/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/1.00  --bmc1_ucm_layered_model                none
% 3.23/1.00  --bmc1_ucm_max_lemma_size               10
% 3.23/1.00  
% 3.23/1.00  ------ AIG Options
% 3.23/1.00  
% 3.23/1.00  --aig_mode                              false
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation Options
% 3.23/1.00  
% 3.23/1.00  --instantiation_flag                    true
% 3.23/1.00  --inst_sos_flag                         false
% 3.23/1.00  --inst_sos_phase                        true
% 3.23/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel_side                     num_symb
% 3.23/1.00  --inst_solver_per_active                1400
% 3.23/1.00  --inst_solver_calls_frac                1.
% 3.23/1.00  --inst_passive_queue_type               priority_queues
% 3.23/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/1.00  --inst_passive_queues_freq              [25;2]
% 3.23/1.00  --inst_dismatching                      true
% 3.23/1.00  --inst_eager_unprocessed_to_passive     true
% 3.23/1.00  --inst_prop_sim_given                   true
% 3.23/1.00  --inst_prop_sim_new                     false
% 3.23/1.00  --inst_subs_new                         false
% 3.23/1.00  --inst_eq_res_simp                      false
% 3.23/1.00  --inst_subs_given                       false
% 3.23/1.00  --inst_orphan_elimination               true
% 3.23/1.00  --inst_learning_loop_flag               true
% 3.23/1.00  --inst_learning_start                   3000
% 3.23/1.00  --inst_learning_factor                  2
% 3.23/1.00  --inst_start_prop_sim_after_learn       3
% 3.23/1.00  --inst_sel_renew                        solver
% 3.23/1.00  --inst_lit_activity_flag                true
% 3.23/1.00  --inst_restr_to_given                   false
% 3.23/1.00  --inst_activity_threshold               500
% 3.23/1.00  --inst_out_proof                        true
% 3.23/1.00  
% 3.23/1.00  ------ Resolution Options
% 3.23/1.00  
% 3.23/1.00  --resolution_flag                       true
% 3.23/1.00  --res_lit_sel                           adaptive
% 3.23/1.00  --res_lit_sel_side                      none
% 3.23/1.00  --res_ordering                          kbo
% 3.23/1.00  --res_to_prop_solver                    active
% 3.23/1.00  --res_prop_simpl_new                    false
% 3.23/1.00  --res_prop_simpl_given                  true
% 3.23/1.00  --res_passive_queue_type                priority_queues
% 3.23/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/1.00  --res_passive_queues_freq               [15;5]
% 3.23/1.00  --res_forward_subs                      full
% 3.23/1.00  --res_backward_subs                     full
% 3.23/1.00  --res_forward_subs_resolution           true
% 3.23/1.00  --res_backward_subs_resolution          true
% 3.23/1.00  --res_orphan_elimination                true
% 3.23/1.00  --res_time_limit                        2.
% 3.23/1.00  --res_out_proof                         true
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Options
% 3.23/1.00  
% 3.23/1.00  --superposition_flag                    true
% 3.23/1.00  --sup_passive_queue_type                priority_queues
% 3.23/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.23/1.00  --demod_completeness_check              fast
% 3.23/1.00  --demod_use_ground                      true
% 3.23/1.00  --sup_to_prop_solver                    passive
% 3.23/1.00  --sup_prop_simpl_new                    true
% 3.23/1.00  --sup_prop_simpl_given                  true
% 3.23/1.00  --sup_fun_splitting                     false
% 3.23/1.00  --sup_smt_interval                      50000
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Simplification Setup
% 3.23/1.00  
% 3.23/1.00  --sup_indices_passive                   []
% 3.23/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_full_bw                           [BwDemod]
% 3.23/1.00  --sup_immed_triv                        [TrivRules]
% 3.23/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_immed_bw_main                     []
% 3.23/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  
% 3.23/1.00  ------ Combination Options
% 3.23/1.00  
% 3.23/1.00  --comb_res_mult                         3
% 3.23/1.00  --comb_sup_mult                         2
% 3.23/1.00  --comb_inst_mult                        10
% 3.23/1.00  
% 3.23/1.00  ------ Debug Options
% 3.23/1.00  
% 3.23/1.00  --dbg_backtrace                         false
% 3.23/1.00  --dbg_dump_prop_clauses                 false
% 3.23/1.00  --dbg_dump_prop_clauses_file            -
% 3.23/1.00  --dbg_out_stat                          false
% 3.23/1.00  ------ Parsing...
% 3.23/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.23/1.00  ------ Proving...
% 3.23/1.00  ------ Problem Properties 
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  clauses                                 32
% 3.23/1.00  conjectures                             3
% 3.23/1.00  EPR                                     5
% 3.23/1.00  Horn                                    27
% 3.23/1.00  unary                                   4
% 3.23/1.00  binary                                  13
% 3.23/1.00  lits                                    86
% 3.23/1.00  lits eq                                 31
% 3.23/1.00  fd_pure                                 0
% 3.23/1.00  fd_pseudo                               0
% 3.23/1.00  fd_cond                                 2
% 3.23/1.00  fd_pseudo_cond                          0
% 3.23/1.00  AC symbols                              0
% 3.23/1.00  
% 3.23/1.00  ------ Schedule dynamic 5 is on 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  ------ 
% 3.23/1.00  Current options:
% 3.23/1.00  ------ 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options
% 3.23/1.00  
% 3.23/1.00  --out_options                           all
% 3.23/1.00  --tptp_safe_out                         true
% 3.23/1.00  --problem_path                          ""
% 3.23/1.00  --include_path                          ""
% 3.23/1.00  --clausifier                            res/vclausify_rel
% 3.23/1.00  --clausifier_options                    --mode clausify
% 3.23/1.00  --stdin                                 false
% 3.23/1.00  --stats_out                             all
% 3.23/1.00  
% 3.23/1.00  ------ General Options
% 3.23/1.00  
% 3.23/1.00  --fof                                   false
% 3.23/1.00  --time_out_real                         305.
% 3.23/1.00  --time_out_virtual                      -1.
% 3.23/1.00  --symbol_type_check                     false
% 3.23/1.00  --clausify_out                          false
% 3.23/1.00  --sig_cnt_out                           false
% 3.23/1.00  --trig_cnt_out                          false
% 3.23/1.00  --trig_cnt_out_tolerance                1.
% 3.23/1.00  --trig_cnt_out_sk_spl                   false
% 3.23/1.00  --abstr_cl_out                          false
% 3.23/1.00  
% 3.23/1.00  ------ Global Options
% 3.23/1.00  
% 3.23/1.00  --schedule                              default
% 3.23/1.00  --add_important_lit                     false
% 3.23/1.00  --prop_solver_per_cl                    1000
% 3.23/1.00  --min_unsat_core                        false
% 3.23/1.00  --soft_assumptions                      false
% 3.23/1.00  --soft_lemma_size                       3
% 3.23/1.00  --prop_impl_unit_size                   0
% 3.23/1.00  --prop_impl_unit                        []
% 3.23/1.00  --share_sel_clauses                     true
% 3.23/1.00  --reset_solvers                         false
% 3.23/1.00  --bc_imp_inh                            [conj_cone]
% 3.23/1.00  --conj_cone_tolerance                   3.
% 3.23/1.00  --extra_neg_conj                        none
% 3.23/1.00  --large_theory_mode                     true
% 3.23/1.00  --prolific_symb_bound                   200
% 3.23/1.00  --lt_threshold                          2000
% 3.23/1.00  --clause_weak_htbl                      true
% 3.23/1.00  --gc_record_bc_elim                     false
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing Options
% 3.23/1.00  
% 3.23/1.00  --preprocessing_flag                    true
% 3.23/1.00  --time_out_prep_mult                    0.1
% 3.23/1.00  --splitting_mode                        input
% 3.23/1.00  --splitting_grd                         true
% 3.23/1.00  --splitting_cvd                         false
% 3.23/1.00  --splitting_cvd_svl                     false
% 3.23/1.00  --splitting_nvd                         32
% 3.23/1.00  --sub_typing                            true
% 3.23/1.00  --prep_gs_sim                           true
% 3.23/1.00  --prep_unflatten                        true
% 3.23/1.00  --prep_res_sim                          true
% 3.23/1.00  --prep_upred                            true
% 3.23/1.00  --prep_sem_filter                       exhaustive
% 3.23/1.00  --prep_sem_filter_out                   false
% 3.23/1.00  --pred_elim                             true
% 3.23/1.00  --res_sim_input                         true
% 3.23/1.00  --eq_ax_congr_red                       true
% 3.23/1.00  --pure_diseq_elim                       true
% 3.23/1.00  --brand_transform                       false
% 3.23/1.00  --non_eq_to_eq                          false
% 3.23/1.00  --prep_def_merge                        true
% 3.23/1.00  --prep_def_merge_prop_impl              false
% 3.23/1.00  --prep_def_merge_mbd                    true
% 3.23/1.00  --prep_def_merge_tr_red                 false
% 3.23/1.00  --prep_def_merge_tr_cl                  false
% 3.23/1.00  --smt_preprocessing                     true
% 3.23/1.00  --smt_ac_axioms                         fast
% 3.23/1.00  --preprocessed_out                      false
% 3.23/1.00  --preprocessed_stats                    false
% 3.23/1.00  
% 3.23/1.00  ------ Abstraction refinement Options
% 3.23/1.00  
% 3.23/1.00  --abstr_ref                             []
% 3.23/1.00  --abstr_ref_prep                        false
% 3.23/1.00  --abstr_ref_until_sat                   false
% 3.23/1.00  --abstr_ref_sig_restrict                funpre
% 3.23/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/1.00  --abstr_ref_under                       []
% 3.23/1.00  
% 3.23/1.00  ------ SAT Options
% 3.23/1.00  
% 3.23/1.00  --sat_mode                              false
% 3.23/1.00  --sat_fm_restart_options                ""
% 3.23/1.00  --sat_gr_def                            false
% 3.23/1.00  --sat_epr_types                         true
% 3.23/1.00  --sat_non_cyclic_types                  false
% 3.23/1.00  --sat_finite_models                     false
% 3.23/1.00  --sat_fm_lemmas                         false
% 3.23/1.00  --sat_fm_prep                           false
% 3.23/1.00  --sat_fm_uc_incr                        true
% 3.23/1.00  --sat_out_model                         small
% 3.23/1.00  --sat_out_clauses                       false
% 3.23/1.00  
% 3.23/1.00  ------ QBF Options
% 3.23/1.00  
% 3.23/1.00  --qbf_mode                              false
% 3.23/1.00  --qbf_elim_univ                         false
% 3.23/1.00  --qbf_dom_inst                          none
% 3.23/1.00  --qbf_dom_pre_inst                      false
% 3.23/1.00  --qbf_sk_in                             false
% 3.23/1.00  --qbf_pred_elim                         true
% 3.23/1.00  --qbf_split                             512
% 3.23/1.00  
% 3.23/1.00  ------ BMC1 Options
% 3.23/1.00  
% 3.23/1.00  --bmc1_incremental                      false
% 3.23/1.00  --bmc1_axioms                           reachable_all
% 3.23/1.00  --bmc1_min_bound                        0
% 3.23/1.00  --bmc1_max_bound                        -1
% 3.23/1.00  --bmc1_max_bound_default                -1
% 3.23/1.00  --bmc1_symbol_reachability              true
% 3.23/1.00  --bmc1_property_lemmas                  false
% 3.23/1.00  --bmc1_k_induction                      false
% 3.23/1.00  --bmc1_non_equiv_states                 false
% 3.23/1.00  --bmc1_deadlock                         false
% 3.23/1.00  --bmc1_ucm                              false
% 3.23/1.00  --bmc1_add_unsat_core                   none
% 3.23/1.00  --bmc1_unsat_core_children              false
% 3.23/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/1.00  --bmc1_out_stat                         full
% 3.23/1.00  --bmc1_ground_init                      false
% 3.23/1.00  --bmc1_pre_inst_next_state              false
% 3.23/1.00  --bmc1_pre_inst_state                   false
% 3.23/1.00  --bmc1_pre_inst_reach_state             false
% 3.23/1.00  --bmc1_out_unsat_core                   false
% 3.23/1.00  --bmc1_aig_witness_out                  false
% 3.23/1.00  --bmc1_verbose                          false
% 3.23/1.00  --bmc1_dump_clauses_tptp                false
% 3.23/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.23/1.00  --bmc1_dump_file                        -
% 3.23/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.23/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.23/1.00  --bmc1_ucm_extend_mode                  1
% 3.23/1.00  --bmc1_ucm_init_mode                    2
% 3.23/1.00  --bmc1_ucm_cone_mode                    none
% 3.23/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.23/1.00  --bmc1_ucm_relax_model                  4
% 3.23/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.23/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/1.00  --bmc1_ucm_layered_model                none
% 3.23/1.00  --bmc1_ucm_max_lemma_size               10
% 3.23/1.00  
% 3.23/1.00  ------ AIG Options
% 3.23/1.00  
% 3.23/1.00  --aig_mode                              false
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation Options
% 3.23/1.00  
% 3.23/1.00  --instantiation_flag                    true
% 3.23/1.00  --inst_sos_flag                         false
% 3.23/1.00  --inst_sos_phase                        true
% 3.23/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel_side                     none
% 3.23/1.00  --inst_solver_per_active                1400
% 3.23/1.00  --inst_solver_calls_frac                1.
% 3.23/1.00  --inst_passive_queue_type               priority_queues
% 3.23/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/1.00  --inst_passive_queues_freq              [25;2]
% 3.23/1.00  --inst_dismatching                      true
% 3.23/1.00  --inst_eager_unprocessed_to_passive     true
% 3.23/1.00  --inst_prop_sim_given                   true
% 3.23/1.00  --inst_prop_sim_new                     false
% 3.23/1.00  --inst_subs_new                         false
% 3.23/1.00  --inst_eq_res_simp                      false
% 3.23/1.00  --inst_subs_given                       false
% 3.23/1.00  --inst_orphan_elimination               true
% 3.23/1.00  --inst_learning_loop_flag               true
% 3.23/1.00  --inst_learning_start                   3000
% 3.23/1.00  --inst_learning_factor                  2
% 3.23/1.00  --inst_start_prop_sim_after_learn       3
% 3.23/1.00  --inst_sel_renew                        solver
% 3.23/1.00  --inst_lit_activity_flag                true
% 3.23/1.00  --inst_restr_to_given                   false
% 3.23/1.00  --inst_activity_threshold               500
% 3.23/1.00  --inst_out_proof                        true
% 3.23/1.00  
% 3.23/1.00  ------ Resolution Options
% 3.23/1.00  
% 3.23/1.00  --resolution_flag                       false
% 3.23/1.00  --res_lit_sel                           adaptive
% 3.23/1.00  --res_lit_sel_side                      none
% 3.23/1.00  --res_ordering                          kbo
% 3.23/1.00  --res_to_prop_solver                    active
% 3.23/1.00  --res_prop_simpl_new                    false
% 3.23/1.00  --res_prop_simpl_given                  true
% 3.23/1.00  --res_passive_queue_type                priority_queues
% 3.23/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/1.00  --res_passive_queues_freq               [15;5]
% 3.23/1.00  --res_forward_subs                      full
% 3.23/1.00  --res_backward_subs                     full
% 3.23/1.00  --res_forward_subs_resolution           true
% 3.23/1.00  --res_backward_subs_resolution          true
% 3.23/1.00  --res_orphan_elimination                true
% 3.23/1.00  --res_time_limit                        2.
% 3.23/1.00  --res_out_proof                         true
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Options
% 3.23/1.00  
% 3.23/1.00  --superposition_flag                    true
% 3.23/1.00  --sup_passive_queue_type                priority_queues
% 3.23/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.23/1.00  --demod_completeness_check              fast
% 3.23/1.00  --demod_use_ground                      true
% 3.23/1.00  --sup_to_prop_solver                    passive
% 3.23/1.00  --sup_prop_simpl_new                    true
% 3.23/1.00  --sup_prop_simpl_given                  true
% 3.23/1.00  --sup_fun_splitting                     false
% 3.23/1.00  --sup_smt_interval                      50000
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Simplification Setup
% 3.23/1.00  
% 3.23/1.00  --sup_indices_passive                   []
% 3.23/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_full_bw                           [BwDemod]
% 3.23/1.00  --sup_immed_triv                        [TrivRules]
% 3.23/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_immed_bw_main                     []
% 3.23/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  
% 3.23/1.00  ------ Combination Options
% 3.23/1.00  
% 3.23/1.00  --comb_res_mult                         3
% 3.23/1.00  --comb_sup_mult                         2
% 3.23/1.00  --comb_inst_mult                        10
% 3.23/1.00  
% 3.23/1.00  ------ Debug Options
% 3.23/1.00  
% 3.23/1.00  --dbg_backtrace                         false
% 3.23/1.00  --dbg_dump_prop_clauses                 false
% 3.23/1.00  --dbg_dump_prop_clauses_file            -
% 3.23/1.00  --dbg_out_stat                          false
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  ------ Proving...
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  % SZS status Theorem for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  fof(f4,axiom,(
% 3.23/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f41,plain,(
% 3.23/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.23/1.00    inference(nnf_transformation,[],[f4])).
% 3.23/1.00  
% 3.23/1.00  fof(f52,plain,(
% 3.23/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f41])).
% 3.23/1.00  
% 3.23/1.00  fof(f12,axiom,(
% 3.23/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f27,plain,(
% 3.23/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(ennf_transformation,[],[f12])).
% 3.23/1.00  
% 3.23/1.00  fof(f28,plain,(
% 3.23/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(flattening,[],[f27])).
% 3.23/1.00  
% 3.23/1.00  fof(f42,plain,(
% 3.23/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(nnf_transformation,[],[f28])).
% 3.23/1.00  
% 3.23/1.00  fof(f63,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f42])).
% 3.23/1.00  
% 3.23/1.00  fof(f14,conjecture,(
% 3.23/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f15,negated_conjecture,(
% 3.23/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.23/1.00    inference(negated_conjecture,[],[f14])).
% 3.23/1.00  
% 3.23/1.00  fof(f31,plain,(
% 3.23/1.00    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.23/1.00    inference(ennf_transformation,[],[f15])).
% 3.23/1.00  
% 3.23/1.00  fof(f32,plain,(
% 3.23/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.23/1.00    inference(flattening,[],[f31])).
% 3.23/1.00  
% 3.23/1.00  fof(f43,plain,(
% 3.23/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f44,plain,(
% 3.23/1.00    (~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f43])).
% 3.23/1.00  
% 3.23/1.00  fof(f73,plain,(
% 3.23/1.00    v1_funct_2(sK4,sK2,sK3)),
% 3.23/1.00    inference(cnf_transformation,[],[f44])).
% 3.23/1.00  
% 3.23/1.00  fof(f74,plain,(
% 3.23/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.23/1.00    inference(cnf_transformation,[],[f44])).
% 3.23/1.00  
% 3.23/1.00  fof(f10,axiom,(
% 3.23/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f25,plain,(
% 3.23/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(ennf_transformation,[],[f10])).
% 3.23/1.00  
% 3.23/1.00  fof(f61,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f25])).
% 3.23/1.00  
% 3.23/1.00  fof(f11,axiom,(
% 3.23/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f26,plain,(
% 3.23/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(ennf_transformation,[],[f11])).
% 3.23/1.00  
% 3.23/1.00  fof(f62,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f26])).
% 3.23/1.00  
% 3.23/1.00  fof(f76,plain,(
% 3.23/1.00    k2_relset_1(sK2,sK3,sK4) = sK3),
% 3.23/1.00    inference(cnf_transformation,[],[f44])).
% 3.23/1.00  
% 3.23/1.00  fof(f13,axiom,(
% 3.23/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f29,plain,(
% 3.23/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.23/1.00    inference(ennf_transformation,[],[f13])).
% 3.23/1.00  
% 3.23/1.00  fof(f30,plain,(
% 3.23/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.23/1.00    inference(flattening,[],[f29])).
% 3.23/1.00  
% 3.23/1.00  fof(f70,plain,(
% 3.23/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f30])).
% 3.23/1.00  
% 3.23/1.00  fof(f77,plain,(
% 3.23/1.00    ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))),
% 3.23/1.00    inference(cnf_transformation,[],[f44])).
% 3.23/1.00  
% 3.23/1.00  fof(f9,axiom,(
% 3.23/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f24,plain,(
% 3.23/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(ennf_transformation,[],[f9])).
% 3.23/1.00  
% 3.23/1.00  fof(f60,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f24])).
% 3.23/1.00  
% 3.23/1.00  fof(f72,plain,(
% 3.23/1.00    v1_funct_1(sK4)),
% 3.23/1.00    inference(cnf_transformation,[],[f44])).
% 3.23/1.00  
% 3.23/1.00  fof(f7,axiom,(
% 3.23/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f20,plain,(
% 3.23/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.23/1.00    inference(ennf_transformation,[],[f7])).
% 3.23/1.00  
% 3.23/1.00  fof(f21,plain,(
% 3.23/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.23/1.00    inference(flattening,[],[f20])).
% 3.23/1.00  
% 3.23/1.00  fof(f57,plain,(
% 3.23/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f21])).
% 3.23/1.00  
% 3.23/1.00  fof(f56,plain,(
% 3.23/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f21])).
% 3.23/1.00  
% 3.23/1.00  fof(f8,axiom,(
% 3.23/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f22,plain,(
% 3.23/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.23/1.00    inference(ennf_transformation,[],[f8])).
% 3.23/1.00  
% 3.23/1.00  fof(f23,plain,(
% 3.23/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.23/1.00    inference(flattening,[],[f22])).
% 3.23/1.00  
% 3.23/1.00  fof(f59,plain,(
% 3.23/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f23])).
% 3.23/1.00  
% 3.23/1.00  fof(f75,plain,(
% 3.23/1.00    v2_funct_1(sK4)),
% 3.23/1.00    inference(cnf_transformation,[],[f44])).
% 3.23/1.00  
% 3.23/1.00  fof(f58,plain,(
% 3.23/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f23])).
% 3.23/1.00  
% 3.23/1.00  fof(f71,plain,(
% 3.23/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f30])).
% 3.23/1.00  
% 3.23/1.00  fof(f5,axiom,(
% 3.23/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f17,plain,(
% 3.23/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.23/1.00    inference(ennf_transformation,[],[f5])).
% 3.23/1.00  
% 3.23/1.00  fof(f18,plain,(
% 3.23/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.23/1.00    inference(flattening,[],[f17])).
% 3.23/1.00  
% 3.23/1.00  fof(f54,plain,(
% 3.23/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f18])).
% 3.23/1.00  
% 3.23/1.00  fof(f1,axiom,(
% 3.23/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f33,plain,(
% 3.23/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.23/1.00    inference(nnf_transformation,[],[f1])).
% 3.23/1.00  
% 3.23/1.00  fof(f34,plain,(
% 3.23/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.23/1.00    inference(rectify,[],[f33])).
% 3.23/1.00  
% 3.23/1.00  fof(f35,plain,(
% 3.23/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f36,plain,(
% 3.23/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 3.23/1.00  
% 3.23/1.00  fof(f45,plain,(
% 3.23/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f36])).
% 3.23/1.00  
% 3.23/1.00  fof(f53,plain,(
% 3.23/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f18])).
% 3.23/1.00  
% 3.23/1.00  fof(f2,axiom,(
% 3.23/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f16,plain,(
% 3.23/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.23/1.00    inference(ennf_transformation,[],[f2])).
% 3.23/1.00  
% 3.23/1.00  fof(f37,plain,(
% 3.23/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.23/1.00    inference(nnf_transformation,[],[f16])).
% 3.23/1.00  
% 3.23/1.00  fof(f38,plain,(
% 3.23/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.23/1.00    inference(rectify,[],[f37])).
% 3.23/1.00  
% 3.23/1.00  fof(f39,plain,(
% 3.23/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f40,plain,(
% 3.23/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 3.23/1.00  
% 3.23/1.00  fof(f48,plain,(
% 3.23/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f40])).
% 3.23/1.00  
% 3.23/1.00  fof(f65,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f42])).
% 3.23/1.00  
% 3.23/1.00  fof(f3,axiom,(
% 3.23/1.00    v1_xboole_0(k1_xboole_0)),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f50,plain,(
% 3.23/1.00    v1_xboole_0(k1_xboole_0)),
% 3.23/1.00    inference(cnf_transformation,[],[f3])).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1192,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3229,plain,
% 3.23/1.00      ( X0 != X1 | k2_relat_1(X2) != X1 | k2_relat_1(X2) = X0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1192]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6183,plain,
% 3.23/1.00      ( k2_relat_1(k2_funct_1(sK4)) != X0
% 3.23/1.00      | k2_relat_1(k2_funct_1(sK4)) = sK2
% 3.23/1.00      | sK2 != X0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_3229]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6184,plain,
% 3.23/1.00      ( k2_relat_1(k2_funct_1(sK4)) = sK2
% 3.23/1.00      | k2_relat_1(k2_funct_1(sK4)) != k1_xboole_0
% 3.23/1.00      | sK2 != k1_xboole_0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_6183]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2947,plain,
% 3.23/1.00      ( k1_relset_1(sK3,sK2,k2_funct_1(sK4)) != X0
% 3.23/1.00      | k1_relset_1(sK3,sK2,k2_funct_1(sK4)) = sK3
% 3.23/1.00      | sK3 != X0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1192]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4644,plain,
% 3.23/1.00      ( k1_relset_1(sK3,sK2,k2_funct_1(sK4)) != k1_relat_1(k2_funct_1(sK4))
% 3.23/1.00      | k1_relset_1(sK3,sK2,k2_funct_1(sK4)) = sK3
% 3.23/1.00      | sK3 != k1_relat_1(k2_funct_1(sK4)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2947]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6,plain,
% 3.23/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1920,plain,
% 3.23/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.23/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_23,plain,
% 3.23/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.23/1.00      | k1_xboole_0 = X2 ),
% 3.23/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_31,negated_conjecture,
% 3.23/1.00      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.23/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_719,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.23/1.00      | sK2 != X1
% 3.23/1.00      | sK3 != X2
% 3.23/1.00      | sK4 != X0
% 3.23/1.00      | k1_xboole_0 = X2 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_720,plain,
% 3.23/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.23/1.00      | k1_relset_1(sK2,sK3,sK4) = sK2
% 3.23/1.00      | k1_xboole_0 = sK3 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_719]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_30,negated_conjecture,
% 3.23/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.23/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_722,plain,
% 3.23/1.00      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_720,c_30]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1909,plain,
% 3.23/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_16,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1912,plain,
% 3.23/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.23/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3469,plain,
% 3.23/1.00      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1909,c_1912]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3679,plain,
% 3.23/1.00      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_722,c_3469]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_17,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1911,plain,
% 3.23/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.23/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3042,plain,
% 3.23/1.00      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1909,c_1911]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_28,negated_conjecture,
% 3.23/1.00      ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
% 3.23/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3044,plain,
% 3.23/1.00      ( k2_relat_1(sK4) = sK3 ),
% 3.23/1.00      inference(light_normalisation,[status(thm)],[c_3042,c_28]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_25,plain,
% 3.23/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_relat_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_27,negated_conjecture,
% 3.23/1.00      ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
% 3.23/1.00      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.23/1.00      | ~ v1_funct_1(k2_funct_1(sK4)) ),
% 3.23/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_730,plain,
% 3.23/1.00      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.23/1.00      | ~ v1_relat_1(X0)
% 3.23/1.00      | k2_funct_1(sK4) != X0
% 3.23/1.00      | k1_relat_1(X0) != sK3
% 3.23/1.00      | k2_relat_1(X0) != sK2 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_27]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_731,plain,
% 3.23/1.00      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.23/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.23/1.00      | ~ v1_relat_1(k2_funct_1(sK4))
% 3.23/1.00      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.23/1.00      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_730]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_15,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | v1_relat_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_743,plain,
% 3.23/1.00      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.23/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.23/1.00      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.23/1.00      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 3.23/1.00      inference(forward_subsumption_resolution,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_731,c_15]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1898,plain,
% 3.23/1.00      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.23/1.00      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.23/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.23/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_32,negated_conjecture,
% 3.23/1.00      ( v1_funct_1(sK4) ),
% 3.23/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_33,plain,
% 3.23/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_35,plain,
% 3.23/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_732,plain,
% 3.23/1.00      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.23/1.00      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.23/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.23/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.23/1.00      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2179,plain,
% 3.23/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.23/1.00      | v1_relat_1(sK4) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2180,plain,
% 3.23/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.23/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_2179]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_11,plain,
% 3.23/1.00      ( ~ v1_funct_1(X0)
% 3.23/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.23/1.00      | ~ v1_relat_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2225,plain,
% 3.23/1.00      ( v1_funct_1(k2_funct_1(sK4))
% 3.23/1.00      | ~ v1_funct_1(sK4)
% 3.23/1.00      | ~ v1_relat_1(sK4) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2226,plain,
% 3.23/1.00      ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 3.23/1.00      | v1_funct_1(sK4) != iProver_top
% 3.23/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_2225]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_12,plain,
% 3.23/1.00      ( ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_relat_1(X0)
% 3.23/1.00      | v1_relat_1(k2_funct_1(X0)) ),
% 3.23/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2224,plain,
% 3.23/1.00      ( ~ v1_funct_1(sK4)
% 3.23/1.00      | v1_relat_1(k2_funct_1(sK4))
% 3.23/1.00      | ~ v1_relat_1(sK4) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2228,plain,
% 3.23/1.00      ( v1_funct_1(sK4) != iProver_top
% 3.23/1.00      | v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 3.23/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_2224]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2239,plain,
% 3.23/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.23/1.00      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.23/1.00      | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_1898,c_33,c_35,c_732,c_2180,c_2226,c_2228]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2240,plain,
% 3.23/1.00      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.23/1.00      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.23/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.23/1.00      inference(renaming,[status(thm)],[c_2239]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_13,plain,
% 3.23/1.00      ( ~ v2_funct_1(X0)
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_relat_1(X0)
% 3.23/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_29,negated_conjecture,
% 3.23/1.00      ( v2_funct_1(sK4) ),
% 3.23/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_476,plain,
% 3.23/1.00      ( ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_relat_1(X0)
% 3.23/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.23/1.00      | sK4 != X0 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_477,plain,
% 3.23/1.00      ( ~ v1_funct_1(sK4)
% 3.23/1.00      | ~ v1_relat_1(sK4)
% 3.23/1.00      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_476]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_479,plain,
% 3.23/1.00      ( ~ v1_relat_1(sK4)
% 3.23/1.00      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_477,c_32]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1906,plain,
% 3.23/1.00      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 3.23/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2188,plain,
% 3.23/1.00      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_1906,c_32,c_30,c_477,c_2179]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_14,plain,
% 3.23/1.00      ( ~ v2_funct_1(X0)
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_relat_1(X0)
% 3.23/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_462,plain,
% 3.23/1.00      ( ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_relat_1(X0)
% 3.23/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.23/1.00      | sK4 != X0 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_463,plain,
% 3.23/1.00      ( ~ v1_funct_1(sK4)
% 3.23/1.00      | ~ v1_relat_1(sK4)
% 3.23/1.00      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_462]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_465,plain,
% 3.23/1.00      ( ~ v1_relat_1(sK4)
% 3.23/1.00      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_463,c_32]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1907,plain,
% 3.23/1.00      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 3.23/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_465]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2192,plain,
% 3.23/1.00      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_1907,c_32,c_30,c_463,c_2179]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2243,plain,
% 3.23/1.00      ( k1_relat_1(sK4) != sK2
% 3.23/1.00      | k2_relat_1(sK4) != sK3
% 3.23/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.23/1.00      inference(light_normalisation,[status(thm)],[c_2240,c_2188,c_2192]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3099,plain,
% 3.23/1.00      ( k1_relat_1(sK4) != sK2
% 3.23/1.00      | sK3 != sK3
% 3.23/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_3044,c_2243]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3103,plain,
% 3.23/1.00      ( k1_relat_1(sK4) != sK2
% 3.23/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.23/1.00      inference(equality_resolution_simp,[status(thm)],[c_3099]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3817,plain,
% 3.23/1.00      ( sK3 = k1_xboole_0
% 3.23/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_3679,c_3103]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3981,plain,
% 3.23/1.00      ( sK3 = k1_xboole_0
% 3.23/1.00      | r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1920,c_3817]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_24,plain,
% 3.23/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_relat_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1910,plain,
% 3.23/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.23/1.00      | v1_funct_1(X0) != iProver_top
% 3.23/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3423,plain,
% 3.23/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
% 3.23/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.23/1.00      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2188,c_1910]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3100,plain,
% 3.23/1.00      ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_3044,c_2192]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3442,plain,
% 3.23/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
% 3.23/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.23/1.00      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.23/1.00      inference(light_normalisation,[status(thm)],[c_3423,c_3100]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4057,plain,
% 3.23/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_3442,c_33,c_35,c_2180,c_2226,c_2228]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4062,plain,
% 3.23/1.00      ( sK3 = k1_xboole_0
% 3.23/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_3679,c_4057]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4323,plain,
% 3.23/1.00      ( sK3 = k1_xboole_0 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_3981,c_3817,c_4062]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_8,plain,
% 3.23/1.00      ( ~ v1_relat_1(X0)
% 3.23/1.00      | k2_relat_1(X0) != k1_xboole_0
% 3.23/1.00      | k1_xboole_0 = X0 ),
% 3.23/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1918,plain,
% 3.23/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 3.23/1.00      | k1_xboole_0 = X0
% 3.23/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3111,plain,
% 3.23/1.00      ( sK3 != k1_xboole_0
% 3.23/1.00      | sK4 = k1_xboole_0
% 3.23/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_3044,c_1918]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3112,plain,
% 3.23/1.00      ( ~ v1_relat_1(sK4) | sK3 != k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.23/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3111]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3181,plain,
% 3.23/1.00      ( sK4 = k1_xboole_0 | sK3 != k1_xboole_0 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_3111,c_30,c_2179,c_3112]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3182,plain,
% 3.23/1.00      ( sK3 != k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.23/1.00      inference(renaming,[status(thm)],[c_3181]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4336,plain,
% 3.23/1.00      ( sK4 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_4323,c_3182]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4394,plain,
% 3.23/1.00      ( sK4 = k1_xboole_0 ),
% 3.23/1.00      inference(equality_resolution_simp,[status(thm)],[c_4336]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4339,plain,
% 3.23/1.00      ( k2_relat_1(sK4) = k1_xboole_0 ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_4323,c_3044]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4398,plain,
% 3.23/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_4394,c_4339]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1197,plain,
% 3.23/1.00      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 3.23/1.00      theory(equality) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4038,plain,
% 3.23/1.00      ( k2_funct_1(sK4) != X0
% 3.23/1.00      | k2_relat_1(k2_funct_1(sK4)) = k2_relat_1(X0) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1197]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4040,plain,
% 3.23/1.00      ( k2_funct_1(sK4) != k1_xboole_0
% 3.23/1.00      | k2_relat_1(k2_funct_1(sK4)) = k2_relat_1(k1_xboole_0) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_4038]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3156,plain,
% 3.23/1.00      ( k2_relat_1(k2_funct_1(sK4)) != X0
% 3.23/1.00      | k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
% 3.23/1.00      | k1_xboole_0 != X0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1192]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4037,plain,
% 3.23/1.00      ( k2_relat_1(k2_funct_1(sK4)) != k2_relat_1(X0)
% 3.23/1.00      | k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
% 3.23/1.00      | k1_xboole_0 != k2_relat_1(X0) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_3156]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4039,plain,
% 3.23/1.00      ( k2_relat_1(k2_funct_1(sK4)) != k2_relat_1(k1_xboole_0)
% 3.23/1.00      | k2_relat_1(k2_funct_1(sK4)) = k1_xboole_0
% 3.23/1.00      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_4037]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2866,plain,
% 3.23/1.00      ( X0 != X1 | X0 = k1_relat_1(X2) | k1_relat_1(X2) != X1 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1192]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3406,plain,
% 3.23/1.00      ( X0 = k1_relat_1(k2_funct_1(sK4))
% 3.23/1.00      | X0 != k2_relat_1(sK4)
% 3.23/1.00      | k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2866]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3918,plain,
% 3.23/1.00      ( k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
% 3.23/1.00      | sK3 = k1_relat_1(k2_funct_1(sK4))
% 3.23/1.00      | sK3 != k2_relat_1(sK4) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_3406]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1,plain,
% 3.23/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3133,plain,
% 3.23/1.00      ( ~ r2_hidden(sK1(X0,k2_zfmisc_1(X1,X2)),X0) | ~ v1_xboole_0(X0) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3710,plain,
% 3.23/1.00      ( ~ r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4))
% 3.23/1.00      | ~ v1_xboole_0(k2_funct_1(sK4)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_3133]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3512,plain,
% 3.23/1.00      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.23/1.00      | k1_relset_1(sK3,sK2,k2_funct_1(sK4)) = k1_relat_1(k2_funct_1(sK4)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_9,plain,
% 3.23/1.00      ( ~ v1_relat_1(X0)
% 3.23/1.00      | k1_relat_1(X0) != k1_xboole_0
% 3.23/1.00      | k1_xboole_0 = X0 ),
% 3.23/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1917,plain,
% 3.23/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 3.23/1.00      | k1_xboole_0 = X0
% 3.23/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3114,plain,
% 3.23/1.00      ( k2_funct_1(sK4) = k1_xboole_0
% 3.23/1.00      | sK3 != k1_xboole_0
% 3.23/1.00      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_3100,c_1917]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2310,plain,
% 3.23/1.00      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1192]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2632,plain,
% 3.23/1.00      ( k2_relat_1(sK4) != X0 | sK3 != X0 | sK3 = k2_relat_1(sK4) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2310]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3029,plain,
% 3.23/1.00      ( k2_relat_1(sK4) != sK3 | sK3 = k2_relat_1(sK4) | sK3 != sK3 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2632]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2687,plain,
% 3.23/1.00      ( k2_relat_1(X0) != X1
% 3.23/1.00      | k1_xboole_0 != X1
% 3.23/1.00      | k1_xboole_0 = k2_relat_1(X0) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1192]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2688,plain,
% 3.23/1.00      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 3.23/1.00      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 3.23/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2687]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2315,plain,
% 3.23/1.00      ( X0 != X1 | k1_relat_1(X2) != X1 | k1_relat_1(X2) = X0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1192]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2546,plain,
% 3.23/1.00      ( X0 != k2_relat_1(sK4)
% 3.23/1.00      | k1_relat_1(k2_funct_1(sK4)) = X0
% 3.23/1.00      | k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2315]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2631,plain,
% 3.23/1.00      ( k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
% 3.23/1.00      | k1_relat_1(k2_funct_1(sK4)) = sK3
% 3.23/1.00      | sK3 != k2_relat_1(sK4) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2546]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3,plain,
% 3.23/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2258,plain,
% 3.23/1.00      ( r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.23/1.00      | r2_hidden(sK1(X0,k2_zfmisc_1(X1,X2)),X0) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2574,plain,
% 3.23/1.00      ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2))
% 3.23/1.00      | r2_hidden(sK1(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)),k2_funct_1(sK4)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2258]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2174,plain,
% 3.23/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2502,plain,
% 3.23/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.23/1.00      | ~ r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2174]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1191,plain,( X0 = X0 ),theory(equality) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2309,plain,
% 3.23/1.00      ( sK3 = sK3 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1191]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2306,plain,
% 3.23/1.00      ( sK2 = sK2 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1191]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2196,plain,
% 3.23/1.00      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1192]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2305,plain,
% 3.23/1.00      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2196]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1193,plain,
% 3.23/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.23/1.00      theory(equality) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2253,plain,
% 3.23/1.00      ( ~ v1_xboole_0(X0)
% 3.23/1.00      | v1_xboole_0(k2_funct_1(sK4))
% 3.23/1.00      | k2_funct_1(sK4) != X0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1193]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2255,plain,
% 3.23/1.00      ( v1_xboole_0(k2_funct_1(sK4))
% 3.23/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 3.23/1.00      | k2_funct_1(sK4) != k1_xboole_0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_2253]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1218,plain,
% 3.23/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1191]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_21,plain,
% 3.23/1.00      ( v1_funct_2(X0,X1,X2)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.23/1.00      | k1_xboole_0 = X2 ),
% 3.23/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_703,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.23/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.23/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.23/1.00      | k2_funct_1(sK4) != X0
% 3.23/1.00      | sK2 != X2
% 3.23/1.00      | sK3 != X1
% 3.23/1.00      | k1_xboole_0 = X2 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_704,plain,
% 3.23/1.00      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.23/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.23/1.00      | k1_relset_1(sK3,sK2,k2_funct_1(sK4)) != sK3
% 3.23/1.00      | k1_xboole_0 = sK2 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_703]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5,plain,
% 3.23/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(contradiction,plain,
% 3.23/1.00      ( $false ),
% 3.23/1.00      inference(minisat,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_6184,c_4644,c_4398,c_4323,c_4040,c_4039,c_3918,c_3710,
% 3.23/1.00                 c_3512,c_3114,c_3044,c_3029,c_2688,c_2631,c_2574,c_2502,
% 3.23/1.00                 c_2309,c_2306,c_2305,c_2255,c_2228,c_2224,c_2225,c_2180,
% 3.23/1.00                 c_2179,c_1218,c_731,c_704,c_463,c_5,c_35,c_30,c_33,c_32]) ).
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  ------                               Statistics
% 3.23/1.00  
% 3.23/1.00  ------ General
% 3.23/1.00  
% 3.23/1.00  abstr_ref_over_cycles:                  0
% 3.23/1.00  abstr_ref_under_cycles:                 0
% 3.23/1.00  gc_basic_clause_elim:                   0
% 3.23/1.00  forced_gc_time:                         0
% 3.23/1.00  parsing_time:                           0.013
% 3.23/1.00  unif_index_cands_time:                  0.
% 3.23/1.00  unif_index_add_time:                    0.
% 3.23/1.00  orderings_time:                         0.
% 3.23/1.00  out_proof_time:                         0.013
% 3.23/1.00  total_time:                             0.235
% 3.23/1.00  num_of_symbols:                         52
% 3.23/1.00  num_of_terms:                           3501
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing
% 3.23/1.00  
% 3.23/1.00  num_of_splits:                          0
% 3.23/1.00  num_of_split_atoms:                     0
% 3.23/1.00  num_of_reused_defs:                     0
% 3.23/1.00  num_eq_ax_congr_red:                    20
% 3.23/1.00  num_of_sem_filtered_clauses:            1
% 3.23/1.00  num_of_subtypes:                        0
% 3.23/1.00  monotx_restored_types:                  0
% 3.23/1.00  sat_num_of_epr_types:                   0
% 3.23/1.00  sat_num_of_non_cyclic_types:            0
% 3.23/1.00  sat_guarded_non_collapsed_types:        0
% 3.23/1.00  num_pure_diseq_elim:                    0
% 3.23/1.00  simp_replaced_by:                       0
% 3.23/1.00  res_preprocessed:                       157
% 3.23/1.00  prep_upred:                             0
% 3.23/1.00  prep_unflattend:                        49
% 3.23/1.00  smt_new_axioms:                         0
% 3.23/1.00  pred_elim_cands:                        6
% 3.23/1.00  pred_elim:                              2
% 3.23/1.00  pred_elim_cl:                           0
% 3.23/1.00  pred_elim_cycles:                       7
% 3.23/1.00  merged_defs:                            8
% 3.23/1.00  merged_defs_ncl:                        0
% 3.23/1.00  bin_hyper_res:                          8
% 3.23/1.00  prep_cycles:                            4
% 3.23/1.00  pred_elim_time:                         0.011
% 3.23/1.00  splitting_time:                         0.
% 3.23/1.00  sem_filter_time:                        0.
% 3.23/1.00  monotx_time:                            0.
% 3.23/1.00  subtype_inf_time:                       0.
% 3.23/1.00  
% 3.23/1.00  ------ Problem properties
% 3.23/1.00  
% 3.23/1.00  clauses:                                32
% 3.23/1.00  conjectures:                            3
% 3.23/1.00  epr:                                    5
% 3.23/1.00  horn:                                   27
% 3.23/1.00  ground:                                 14
% 3.23/1.00  unary:                                  4
% 3.23/1.00  binary:                                 13
% 3.23/1.00  lits:                                   86
% 3.23/1.00  lits_eq:                                31
% 3.23/1.00  fd_pure:                                0
% 3.23/1.00  fd_pseudo:                              0
% 3.23/1.00  fd_cond:                                2
% 3.23/1.00  fd_pseudo_cond:                         0
% 3.23/1.00  ac_symbols:                             0
% 3.23/1.00  
% 3.23/1.00  ------ Propositional Solver
% 3.23/1.00  
% 3.23/1.00  prop_solver_calls:                      29
% 3.23/1.00  prop_fast_solver_calls:                 1213
% 3.23/1.00  smt_solver_calls:                       0
% 3.23/1.00  smt_fast_solver_calls:                  0
% 3.23/1.00  prop_num_of_clauses:                    1811
% 3.23/1.00  prop_preprocess_simplified:             6302
% 3.23/1.00  prop_fo_subsumed:                       40
% 3.23/1.00  prop_solver_time:                       0.
% 3.23/1.00  smt_solver_time:                        0.
% 3.23/1.00  smt_fast_solver_time:                   0.
% 3.23/1.00  prop_fast_solver_time:                  0.
% 3.23/1.00  prop_unsat_core_time:                   0.
% 3.23/1.00  
% 3.23/1.00  ------ QBF
% 3.23/1.00  
% 3.23/1.00  qbf_q_res:                              0
% 3.23/1.00  qbf_num_tautologies:                    0
% 3.23/1.00  qbf_prep_cycles:                        0
% 3.23/1.00  
% 3.23/1.00  ------ BMC1
% 3.23/1.00  
% 3.23/1.00  bmc1_current_bound:                     -1
% 3.23/1.00  bmc1_last_solved_bound:                 -1
% 3.23/1.00  bmc1_unsat_core_size:                   -1
% 3.23/1.00  bmc1_unsat_core_parents_size:           -1
% 3.23/1.00  bmc1_merge_next_fun:                    0
% 3.23/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation
% 3.23/1.00  
% 3.23/1.00  inst_num_of_clauses:                    653
% 3.23/1.00  inst_num_in_passive:                    52
% 3.23/1.00  inst_num_in_active:                     344
% 3.23/1.00  inst_num_in_unprocessed:                256
% 3.23/1.00  inst_num_of_loops:                      506
% 3.23/1.00  inst_num_of_learning_restarts:          0
% 3.23/1.00  inst_num_moves_active_passive:          156
% 3.23/1.00  inst_lit_activity:                      0
% 3.23/1.00  inst_lit_activity_moves:                0
% 3.23/1.00  inst_num_tautologies:                   0
% 3.23/1.00  inst_num_prop_implied:                  0
% 3.23/1.00  inst_num_existing_simplified:           0
% 3.23/1.00  inst_num_eq_res_simplified:             0
% 3.23/1.00  inst_num_child_elim:                    0
% 3.23/1.00  inst_num_of_dismatching_blockings:      218
% 3.23/1.00  inst_num_of_non_proper_insts:           656
% 3.23/1.00  inst_num_of_duplicates:                 0
% 3.23/1.00  inst_inst_num_from_inst_to_res:         0
% 3.23/1.00  inst_dismatching_checking_time:         0.
% 3.23/1.00  
% 3.23/1.00  ------ Resolution
% 3.23/1.00  
% 3.23/1.00  res_num_of_clauses:                     0
% 3.23/1.00  res_num_in_passive:                     0
% 3.23/1.00  res_num_in_active:                      0
% 3.23/1.00  res_num_of_loops:                       161
% 3.23/1.00  res_forward_subset_subsumed:            25
% 3.23/1.00  res_backward_subset_subsumed:           6
% 3.23/1.00  res_forward_subsumed:                   0
% 3.23/1.00  res_backward_subsumed:                  0
% 3.23/1.00  res_forward_subsumption_resolution:     2
% 3.23/1.00  res_backward_subsumption_resolution:    0
% 3.23/1.00  res_clause_to_clause_subsumption:       293
% 3.23/1.00  res_orphan_elimination:                 0
% 3.23/1.00  res_tautology_del:                      136
% 3.23/1.00  res_num_eq_res_simplified:              0
% 3.23/1.00  res_num_sel_changes:                    0
% 3.23/1.00  res_moves_from_active_to_pass:          0
% 3.23/1.00  
% 3.23/1.00  ------ Superposition
% 3.23/1.00  
% 3.23/1.00  sup_time_total:                         0.
% 3.23/1.00  sup_time_generating:                    0.
% 3.23/1.00  sup_time_sim_full:                      0.
% 3.23/1.00  sup_time_sim_immed:                     0.
% 3.23/1.00  
% 3.23/1.00  sup_num_of_clauses:                     77
% 3.23/1.00  sup_num_in_active:                      46
% 3.23/1.00  sup_num_in_passive:                     31
% 3.23/1.00  sup_num_of_loops:                       100
% 3.23/1.00  sup_fw_superposition:                   53
% 3.23/1.00  sup_bw_superposition:                   82
% 3.23/1.00  sup_immediate_simplified:               65
% 3.23/1.00  sup_given_eliminated:                   0
% 3.23/1.00  comparisons_done:                       0
% 3.23/1.00  comparisons_avoided:                    7
% 3.23/1.00  
% 3.23/1.00  ------ Simplifications
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  sim_fw_subset_subsumed:                 14
% 3.23/1.00  sim_bw_subset_subsumed:                 9
% 3.23/1.00  sim_fw_subsumed:                        4
% 3.23/1.00  sim_bw_subsumed:                        2
% 3.23/1.00  sim_fw_subsumption_res:                 1
% 3.23/1.00  sim_bw_subsumption_res:                 0
% 3.23/1.00  sim_tautology_del:                      7
% 3.23/1.00  sim_eq_tautology_del:                   10
% 3.23/1.00  sim_eq_res_simp:                        7
% 3.23/1.00  sim_fw_demodulated:                     0
% 3.23/1.00  sim_bw_demodulated:                     66
% 3.23/1.00  sim_light_normalised:                   43
% 3.23/1.00  sim_joinable_taut:                      0
% 3.23/1.00  sim_joinable_simp:                      0
% 3.23/1.00  sim_ac_normalised:                      0
% 3.23/1.00  sim_smt_subsumption:                    0
% 3.23/1.00  
%------------------------------------------------------------------------------
