%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:24 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  247 (7104 expanded)
%              Number of clauses        :  171 (2258 expanded)
%              Number of leaves         :   22 (1388 expanded)
%              Depth                    :   23
%              Number of atoms          :  774 (38413 expanded)
%              Number of equality atoms :  380 (7424 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f60,plain,
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

fof(f61,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
      | ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
      | ~ v1_funct_1(k2_funct_1(sK5)) )
    & k2_relset_1(sK3,sK4,sK5) = sK4
    & v2_funct_1(sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f45,f60])).

fof(f100,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f101,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f61])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f81,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f102,plain,(
    v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f99,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f77,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f103,plain,(
    k2_relset_1(sK3,sK4,sK5) = sK4 ),
    inference(cnf_transformation,[],[f61])).

fof(f80,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f97,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f104,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
    | ~ v1_funct_1(k2_funct_1(sK5)) ),
    inference(cnf_transformation,[],[f61])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f109,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f90])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f51,f52])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4319,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_9963,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_4319])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_806,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X1
    | sK4 != X2
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_41])).

cnf(c_807,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_806])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_809,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_807,c_40])).

cnf(c_1832,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1838,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3476,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1832,c_1838])).

cnf(c_3622,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_809,c_3476])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_39,negated_conjecture,
    ( v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_548,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_39])).

cnf(c_549,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_551,plain,
    ( ~ v1_relat_1(sK5)
    | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_549,c_42])).

cnf(c_1829,plain,
    ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_551])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1910,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2007,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1910])).

cnf(c_2070,plain,
    ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1829,c_42,c_40,c_549,c_2007])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1841,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4382,plain,
    ( k9_relat_1(k2_funct_1(sK5),k10_relat_1(k2_funct_1(sK5),X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2070,c_1841])).

cnf(c_43,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_45,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1929,plain,
    ( v1_funct_1(k2_funct_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1930,plain,
    ( v1_funct_1(k2_funct_1(sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1929])).

cnf(c_2008,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2007])).

cnf(c_5051,plain,
    ( r1_tarski(X0,k1_relat_1(sK5)) != iProver_top
    | k9_relat_1(k2_funct_1(sK5),k10_relat_1(k2_funct_1(sK5),X0)) = X0
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4382,c_43,c_45,c_1930,c_2008])).

cnf(c_5052,plain,
    ( k9_relat_1(k2_funct_1(sK5),k10_relat_1(k2_funct_1(sK5),X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5051])).

cnf(c_5059,plain,
    ( k9_relat_1(k2_funct_1(sK5),k10_relat_1(k2_funct_1(sK5),X0)) = X0
    | sK4 = k1_xboole_0
    | r1_tarski(X0,sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3622,c_5052])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1842,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_34,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1833,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3830,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK5)),k1_relat_1(sK5)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2070,c_1833])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1837,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3430,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1832,c_1837])).

cnf(c_38,negated_conjecture,
    ( k2_relset_1(sK3,sK4,sK5) = sK4 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3431,plain,
    ( k2_relat_1(sK5) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_3430,c_38])).

cnf(c_19,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_534,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_39])).

cnf(c_535,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_537,plain,
    ( ~ v1_relat_1(sK5)
    | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_42])).

cnf(c_1830,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_2073,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1830,c_42,c_40,c_535,c_2007])).

cnf(c_3467,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = sK4 ),
    inference(demodulation,[status(thm)],[c_3431,c_2073])).

cnf(c_3835,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k1_relat_1(sK5)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3830,c_3467])).

cnf(c_4824,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k1_relat_1(sK5)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3835,c_43,c_45,c_1930,c_2008])).

cnf(c_4828,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3622,c_4824])).

cnf(c_35,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_37,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
    | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_830,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK5))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK5) != X0
    | k2_relat_1(X0) != sK3
    | k1_relat_1(X0) != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_37])).

cnf(c_831,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | ~ v1_relat_1(k2_funct_1(sK5))
    | k2_relat_1(k2_funct_1(sK5)) != sK3
    | k1_relat_1(k2_funct_1(sK5)) != sK4 ),
    inference(unflattening,[status(thm)],[c_830])).

cnf(c_843,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k2_relat_1(k2_funct_1(sK5)) != sK3
    | k1_relat_1(k2_funct_1(sK5)) != sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_831,c_20])).

cnf(c_1818,plain,
    ( k2_relat_1(k2_funct_1(sK5)) != sK3
    | k1_relat_1(k2_funct_1(sK5)) != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_843])).

cnf(c_848,plain,
    ( k2_relat_1(k2_funct_1(sK5)) != sK3
    | k1_relat_1(k2_funct_1(sK5)) != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_843])).

cnf(c_2336,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | k1_relat_1(k2_funct_1(sK5)) != sK4
    | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1818,c_43,c_45,c_848,c_1930,c_2008])).

cnf(c_2337,plain,
    ( k2_relat_1(k2_funct_1(sK5)) != sK3
    | k1_relat_1(k2_funct_1(sK5)) != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2336])).

cnf(c_2340,plain,
    ( k2_relat_1(sK5) != sK4
    | k1_relat_1(sK5) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2337,c_2070,c_2073])).

cnf(c_3466,plain,
    ( k1_relat_1(sK5) != sK3
    | sK4 != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3431,c_2340])).

cnf(c_3468,plain,
    ( k1_relat_1(sK5) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3466])).

cnf(c_4721,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3622,c_3468])).

cnf(c_5184,plain,
    ( sK4 = k1_xboole_0
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4828,c_4721])).

cnf(c_5188,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_5184])).

cnf(c_5191,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5059,c_43,c_45,c_2008,c_5188])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_668,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X1
    | sK4 != k1_xboole_0
    | sK5 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_41])).

cnf(c_669,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_668])).

cnf(c_1825,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_5215,plain,
    ( sK3 = k1_xboole_0
    | sK5 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5191,c_1825])).

cnf(c_5226,plain,
    ( sK3 = k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5215])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2044,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2045,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top
    | r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2044])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2154,plain,
    ( r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3))
    | r2_hidden(sK1(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)),k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2158,plain,
    ( r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)) = iProver_top
    | r2_hidden(sK1(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)),k2_funct_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2154])).

cnf(c_930,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2057,plain,
    ( k2_relat_1(k2_funct_1(sK5)) != X0
    | k2_relat_1(k2_funct_1(sK5)) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_2280,plain,
    ( k2_relat_1(k2_funct_1(sK5)) != k1_relat_1(sK5)
    | k2_relat_1(k2_funct_1(sK5)) = sK3
    | sK3 != k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2057])).

cnf(c_2064,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_2384,plain,
    ( k1_relat_1(sK5) != X0
    | sK3 != X0
    | sK3 = k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2064])).

cnf(c_2388,plain,
    ( k1_relat_1(sK5) != k1_xboole_0
    | sK3 = k1_relat_1(sK5)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2384])).

cnf(c_2010,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(sK5,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2881,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | ~ r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2010])).

cnf(c_2882,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top
    | r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2881])).

cnf(c_642,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k2_relat_1(X2) != k1_xboole_0
    | k1_relat_1(X2) != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_35])).

cnf(c_643,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_642])).

cnf(c_659,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_643,c_20])).

cnf(c_1826,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_3471,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | sK4 != k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k1_xboole_0))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3431,c_1826])).

cnf(c_4155,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k1_xboole_0))) != iProver_top
    | sK5 = k1_xboole_0
    | sK4 != k1_xboole_0
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3471,c_43])).

cnf(c_4156,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | sK4 != k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k1_xboole_0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4155])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2089,plain,
    ( ~ r2_hidden(X0,k2_funct_1(sK5))
    | ~ v1_xboole_0(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4973,plain,
    ( ~ r2_hidden(sK1(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)),k2_funct_1(sK5))
    | ~ v1_xboole_0(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_2089])).

cnf(c_4974,plain,
    ( r2_hidden(sK1(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)),k2_funct_1(sK5)) != iProver_top
    | v1_xboole_0(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4973])).

cnf(c_3829,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3431,c_1833])).

cnf(c_4096,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3829,c_43,c_45,c_2008])).

cnf(c_5206,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5191,c_4096])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1847,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2827,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1832,c_1847])).

cnf(c_5214,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5191,c_2827])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1839,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4830,plain,
    ( v1_relat_1(k2_funct_1(sK5)) != iProver_top
    | v1_xboole_0(k2_funct_1(sK5)) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4824,c_1839])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_135,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_931,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_6010,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_931])).

cnf(c_6011,plain,
    ( sK4 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6010])).

cnf(c_6013,plain,
    ( sK4 != k1_xboole_0
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6011])).

cnf(c_6475,plain,
    ( v1_xboole_0(k2_funct_1(sK5)) = iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4830,c_43,c_45,c_135,c_2008,c_5188,c_6013])).

cnf(c_6476,plain,
    ( v1_relat_1(k2_funct_1(sK5)) != iProver_top
    | v1_xboole_0(k2_funct_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6475])).

cnf(c_6479,plain,
    ( v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_xboole_0(k2_funct_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_6476])).

cnf(c_7488,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5226,c_42,c_43,c_40,c_45,c_549,c_848,c_1930,c_2007,c_2008,c_2045,c_2158,c_2280,c_2388,c_2882,c_3467,c_4156,c_4974,c_5188,c_5206,c_5214,c_6479])).

cnf(c_7436,plain,
    ( ~ r2_hidden(sK1(X0,k2_funct_1(sK5)),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7438,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,k2_funct_1(sK5)),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7436])).

cnf(c_6594,plain,
    ( ~ r2_hidden(sK1(k2_funct_1(sK5),X0),k2_funct_1(sK5))
    | ~ v1_xboole_0(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_2089])).

cnf(c_6596,plain,
    ( ~ r2_hidden(sK1(k2_funct_1(sK5),k1_xboole_0),k2_funct_1(sK5))
    | ~ v1_xboole_0(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_6594])).

cnf(c_6495,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) = k1_relat_1(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_6480,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | v1_xboole_0(k2_funct_1(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6479])).

cnf(c_849,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k2_funct_1(sK5) != sK5
    | sK3 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_41])).

cnf(c_1817,plain,
    ( k2_funct_1(sK5) != sK5
    | sK3 != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_850,plain,
    ( k2_funct_1(sK5) != sK5
    | sK3 != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_2143,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | sK3 != sK4
    | k2_funct_1(sK5) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1817,c_43,c_45,c_850,c_1930,c_2008])).

cnf(c_2144,plain,
    ( k2_funct_1(sK5) != sK5
    | sK3 != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2143])).

cnf(c_5220,plain,
    ( k2_funct_1(sK5) != sK5
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5191,c_2144])).

cnf(c_2052,plain,
    ( sK3 != X0
    | sK3 = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_2053,plain,
    ( sK3 = sK4
    | sK3 != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2052])).

cnf(c_2145,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | k2_funct_1(sK5) != sK5
    | sK3 != sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2144])).

cnf(c_939,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2202,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK5)
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_939])).

cnf(c_3817,plain,
    ( v1_relat_1(k2_funct_1(sK5))
    | ~ v1_relat_1(sK5)
    | k2_funct_1(sK5) != sK5 ),
    inference(instantiation,[status(thm)],[c_2202])).

cnf(c_4838,plain,
    ( ~ v1_relat_1(k2_funct_1(sK5))
    | v1_xboole_0(k2_funct_1(sK5))
    | ~ v1_xboole_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4830])).

cnf(c_6012,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6010])).

cnf(c_6016,plain,
    ( sK3 != k1_xboole_0
    | k2_funct_1(sK5) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5220,c_43,c_40,c_45,c_5,c_2007,c_2008,c_2044,c_2053,c_2145,c_2154,c_3817,c_4838,c_4973,c_5188,c_6012])).

cnf(c_6017,plain,
    ( k2_funct_1(sK5) != sK5
    | sK3 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6016])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_5536,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2037,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_2664,plain,
    ( k1_relat_1(k2_funct_1(sK5)) != X0
    | sK4 != X0
    | sK4 = k1_relat_1(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_2037])).

cnf(c_4170,plain,
    ( k1_relat_1(k2_funct_1(sK5)) != sK4
    | sK4 = k1_relat_1(k2_funct_1(sK5))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2664])).

cnf(c_929,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3449,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_3262,plain,
    ( r1_tarski(k2_funct_1(sK5),X0)
    | r2_hidden(sK1(k2_funct_1(sK5),X0),k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3269,plain,
    ( r1_tarski(k2_funct_1(sK5),k1_xboole_0)
    | r2_hidden(sK1(k2_funct_1(sK5),k1_xboole_0),k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_3262])).

cnf(c_2766,plain,
    ( r1_tarski(X0,k2_funct_1(sK5))
    | r2_hidden(sK1(X0,k2_funct_1(sK5)),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2773,plain,
    ( r1_tarski(k1_xboole_0,k2_funct_1(sK5))
    | r2_hidden(sK1(k1_xboole_0,k2_funct_1(sK5)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2766])).

cnf(c_2444,plain,
    ( ~ r1_tarski(X0,k2_funct_1(sK5))
    | ~ r1_tarski(k2_funct_1(sK5),X0)
    | k2_funct_1(sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2446,plain,
    ( ~ r1_tarski(k2_funct_1(sK5),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_funct_1(sK5))
    | k2_funct_1(sK5) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2444])).

cnf(c_2228,plain,
    ( k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != X0
    | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_2439,plain,
    ( k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != k1_relat_1(k2_funct_1(sK5))
    | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) = sK4
    | sK4 != k1_relat_1(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_2228])).

cnf(c_2171,plain,
    ( k2_funct_1(sK5) != X0
    | k2_funct_1(sK5) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_2172,plain,
    ( k2_funct_1(sK5) = sK5
    | k2_funct_1(sK5) != k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2171])).

cnf(c_1937,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_2068,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1937])).

cnf(c_27,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_790,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK5) != X0
    | sK3 != X2
    | sK4 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_37])).

cnf(c_791,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != sK4
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_790])).

cnf(c_792,plain,
    ( k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != sK4
    | k1_xboole_0 = sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9963,c_7488,c_7438,c_6596,c_6495,c_6480,c_6479,c_6017,c_5536,c_4974,c_4973,c_4170,c_3467,c_3449,c_3269,c_2773,c_2446,c_2439,c_2172,c_2158,c_2154,c_2068,c_2045,c_2044,c_2008,c_2007,c_1930,c_792,c_5,c_45,c_40,c_43,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.71/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/1.00  
% 3.71/1.00  ------  iProver source info
% 3.71/1.00  
% 3.71/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.71/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/1.00  git: non_committed_changes: false
% 3.71/1.00  git: last_make_outside_of_git: false
% 3.71/1.00  
% 3.71/1.00  ------ 
% 3.71/1.00  
% 3.71/1.00  ------ Input Options
% 3.71/1.00  
% 3.71/1.00  --out_options                           all
% 3.71/1.00  --tptp_safe_out                         true
% 3.71/1.00  --problem_path                          ""
% 3.71/1.00  --include_path                          ""
% 3.71/1.00  --clausifier                            res/vclausify_rel
% 3.71/1.00  --clausifier_options                    ""
% 3.71/1.00  --stdin                                 false
% 3.71/1.00  --stats_out                             all
% 3.71/1.00  
% 3.71/1.00  ------ General Options
% 3.71/1.00  
% 3.71/1.00  --fof                                   false
% 3.71/1.00  --time_out_real                         305.
% 3.71/1.00  --time_out_virtual                      -1.
% 3.71/1.00  --symbol_type_check                     false
% 3.71/1.00  --clausify_out                          false
% 3.71/1.00  --sig_cnt_out                           false
% 3.71/1.00  --trig_cnt_out                          false
% 3.71/1.00  --trig_cnt_out_tolerance                1.
% 3.71/1.00  --trig_cnt_out_sk_spl                   false
% 3.71/1.00  --abstr_cl_out                          false
% 3.71/1.00  
% 3.71/1.00  ------ Global Options
% 3.71/1.00  
% 3.71/1.00  --schedule                              default
% 3.71/1.00  --add_important_lit                     false
% 3.71/1.00  --prop_solver_per_cl                    1000
% 3.71/1.00  --min_unsat_core                        false
% 3.71/1.00  --soft_assumptions                      false
% 3.71/1.00  --soft_lemma_size                       3
% 3.71/1.00  --prop_impl_unit_size                   0
% 3.71/1.00  --prop_impl_unit                        []
% 3.71/1.00  --share_sel_clauses                     true
% 3.71/1.00  --reset_solvers                         false
% 3.71/1.00  --bc_imp_inh                            [conj_cone]
% 3.71/1.00  --conj_cone_tolerance                   3.
% 3.71/1.00  --extra_neg_conj                        none
% 3.71/1.00  --large_theory_mode                     true
% 3.71/1.00  --prolific_symb_bound                   200
% 3.71/1.00  --lt_threshold                          2000
% 3.71/1.00  --clause_weak_htbl                      true
% 3.71/1.00  --gc_record_bc_elim                     false
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing Options
% 3.71/1.00  
% 3.71/1.00  --preprocessing_flag                    true
% 3.71/1.00  --time_out_prep_mult                    0.1
% 3.71/1.00  --splitting_mode                        input
% 3.71/1.00  --splitting_grd                         true
% 3.71/1.00  --splitting_cvd                         false
% 3.71/1.00  --splitting_cvd_svl                     false
% 3.71/1.00  --splitting_nvd                         32
% 3.71/1.00  --sub_typing                            true
% 3.71/1.00  --prep_gs_sim                           true
% 3.71/1.00  --prep_unflatten                        true
% 3.71/1.00  --prep_res_sim                          true
% 3.71/1.00  --prep_upred                            true
% 3.71/1.00  --prep_sem_filter                       exhaustive
% 3.71/1.00  --prep_sem_filter_out                   false
% 3.71/1.00  --pred_elim                             true
% 3.71/1.00  --res_sim_input                         true
% 3.71/1.00  --eq_ax_congr_red                       true
% 3.71/1.00  --pure_diseq_elim                       true
% 3.71/1.00  --brand_transform                       false
% 3.71/1.00  --non_eq_to_eq                          false
% 3.71/1.00  --prep_def_merge                        true
% 3.71/1.00  --prep_def_merge_prop_impl              false
% 3.71/1.00  --prep_def_merge_mbd                    true
% 3.71/1.00  --prep_def_merge_tr_red                 false
% 3.71/1.00  --prep_def_merge_tr_cl                  false
% 3.71/1.00  --smt_preprocessing                     true
% 3.71/1.00  --smt_ac_axioms                         fast
% 3.71/1.00  --preprocessed_out                      false
% 3.71/1.00  --preprocessed_stats                    false
% 3.71/1.00  
% 3.71/1.00  ------ Abstraction refinement Options
% 3.71/1.00  
% 3.71/1.00  --abstr_ref                             []
% 3.71/1.00  --abstr_ref_prep                        false
% 3.71/1.00  --abstr_ref_until_sat                   false
% 3.71/1.00  --abstr_ref_sig_restrict                funpre
% 3.71/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.00  --abstr_ref_under                       []
% 3.71/1.00  
% 3.71/1.00  ------ SAT Options
% 3.71/1.00  
% 3.71/1.00  --sat_mode                              false
% 3.71/1.00  --sat_fm_restart_options                ""
% 3.71/1.00  --sat_gr_def                            false
% 3.71/1.00  --sat_epr_types                         true
% 3.71/1.00  --sat_non_cyclic_types                  false
% 3.71/1.00  --sat_finite_models                     false
% 3.71/1.00  --sat_fm_lemmas                         false
% 3.71/1.00  --sat_fm_prep                           false
% 3.71/1.00  --sat_fm_uc_incr                        true
% 3.71/1.00  --sat_out_model                         small
% 3.71/1.00  --sat_out_clauses                       false
% 3.71/1.00  
% 3.71/1.00  ------ QBF Options
% 3.71/1.00  
% 3.71/1.00  --qbf_mode                              false
% 3.71/1.00  --qbf_elim_univ                         false
% 3.71/1.00  --qbf_dom_inst                          none
% 3.71/1.00  --qbf_dom_pre_inst                      false
% 3.71/1.00  --qbf_sk_in                             false
% 3.71/1.00  --qbf_pred_elim                         true
% 3.71/1.00  --qbf_split                             512
% 3.71/1.00  
% 3.71/1.00  ------ BMC1 Options
% 3.71/1.00  
% 3.71/1.00  --bmc1_incremental                      false
% 3.71/1.00  --bmc1_axioms                           reachable_all
% 3.71/1.00  --bmc1_min_bound                        0
% 3.71/1.00  --bmc1_max_bound                        -1
% 3.71/1.00  --bmc1_max_bound_default                -1
% 3.71/1.00  --bmc1_symbol_reachability              true
% 3.71/1.00  --bmc1_property_lemmas                  false
% 3.71/1.00  --bmc1_k_induction                      false
% 3.71/1.00  --bmc1_non_equiv_states                 false
% 3.71/1.00  --bmc1_deadlock                         false
% 3.71/1.00  --bmc1_ucm                              false
% 3.71/1.00  --bmc1_add_unsat_core                   none
% 3.71/1.00  --bmc1_unsat_core_children              false
% 3.71/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.00  --bmc1_out_stat                         full
% 3.71/1.00  --bmc1_ground_init                      false
% 3.71/1.00  --bmc1_pre_inst_next_state              false
% 3.71/1.00  --bmc1_pre_inst_state                   false
% 3.71/1.00  --bmc1_pre_inst_reach_state             false
% 3.71/1.00  --bmc1_out_unsat_core                   false
% 3.71/1.00  --bmc1_aig_witness_out                  false
% 3.71/1.00  --bmc1_verbose                          false
% 3.71/1.00  --bmc1_dump_clauses_tptp                false
% 3.71/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.00  --bmc1_dump_file                        -
% 3.71/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.00  --bmc1_ucm_extend_mode                  1
% 3.71/1.00  --bmc1_ucm_init_mode                    2
% 3.71/1.00  --bmc1_ucm_cone_mode                    none
% 3.71/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.00  --bmc1_ucm_relax_model                  4
% 3.71/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.00  --bmc1_ucm_layered_model                none
% 3.71/1.00  --bmc1_ucm_max_lemma_size               10
% 3.71/1.00  
% 3.71/1.00  ------ AIG Options
% 3.71/1.00  
% 3.71/1.00  --aig_mode                              false
% 3.71/1.00  
% 3.71/1.00  ------ Instantiation Options
% 3.71/1.00  
% 3.71/1.00  --instantiation_flag                    true
% 3.71/1.00  --inst_sos_flag                         true
% 3.71/1.00  --inst_sos_phase                        true
% 3.71/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel_side                     num_symb
% 3.71/1.00  --inst_solver_per_active                1400
% 3.71/1.00  --inst_solver_calls_frac                1.
% 3.71/1.00  --inst_passive_queue_type               priority_queues
% 3.71/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.00  --inst_passive_queues_freq              [25;2]
% 3.71/1.00  --inst_dismatching                      true
% 3.71/1.00  --inst_eager_unprocessed_to_passive     true
% 3.71/1.00  --inst_prop_sim_given                   true
% 3.71/1.00  --inst_prop_sim_new                     false
% 3.71/1.00  --inst_subs_new                         false
% 3.71/1.00  --inst_eq_res_simp                      false
% 3.71/1.00  --inst_subs_given                       false
% 3.71/1.00  --inst_orphan_elimination               true
% 3.71/1.00  --inst_learning_loop_flag               true
% 3.71/1.00  --inst_learning_start                   3000
% 3.71/1.00  --inst_learning_factor                  2
% 3.71/1.00  --inst_start_prop_sim_after_learn       3
% 3.71/1.00  --inst_sel_renew                        solver
% 3.71/1.00  --inst_lit_activity_flag                true
% 3.71/1.00  --inst_restr_to_given                   false
% 3.71/1.00  --inst_activity_threshold               500
% 3.71/1.00  --inst_out_proof                        true
% 3.71/1.00  
% 3.71/1.00  ------ Resolution Options
% 3.71/1.00  
% 3.71/1.00  --resolution_flag                       true
% 3.71/1.00  --res_lit_sel                           adaptive
% 3.71/1.00  --res_lit_sel_side                      none
% 3.71/1.00  --res_ordering                          kbo
% 3.71/1.00  --res_to_prop_solver                    active
% 3.71/1.00  --res_prop_simpl_new                    false
% 3.71/1.00  --res_prop_simpl_given                  true
% 3.71/1.00  --res_passive_queue_type                priority_queues
% 3.71/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.00  --res_passive_queues_freq               [15;5]
% 3.71/1.00  --res_forward_subs                      full
% 3.71/1.00  --res_backward_subs                     full
% 3.71/1.00  --res_forward_subs_resolution           true
% 3.71/1.00  --res_backward_subs_resolution          true
% 3.71/1.00  --res_orphan_elimination                true
% 3.71/1.00  --res_time_limit                        2.
% 3.71/1.00  --res_out_proof                         true
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Options
% 3.71/1.00  
% 3.71/1.00  --superposition_flag                    true
% 3.71/1.00  --sup_passive_queue_type                priority_queues
% 3.71/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.71/1.00  --demod_completeness_check              fast
% 3.71/1.00  --demod_use_ground                      true
% 3.71/1.00  --sup_to_prop_solver                    passive
% 3.71/1.00  --sup_prop_simpl_new                    true
% 3.71/1.00  --sup_prop_simpl_given                  true
% 3.71/1.00  --sup_fun_splitting                     true
% 3.71/1.00  --sup_smt_interval                      50000
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Simplification Setup
% 3.71/1.00  
% 3.71/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.71/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.71/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.71/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.71/1.00  --sup_immed_triv                        [TrivRules]
% 3.71/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.00  --sup_immed_bw_main                     []
% 3.71/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.71/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.00  --sup_input_bw                          []
% 3.71/1.00  
% 3.71/1.00  ------ Combination Options
% 3.71/1.00  
% 3.71/1.00  --comb_res_mult                         3
% 3.71/1.00  --comb_sup_mult                         2
% 3.71/1.00  --comb_inst_mult                        10
% 3.71/1.00  
% 3.71/1.00  ------ Debug Options
% 3.71/1.00  
% 3.71/1.00  --dbg_backtrace                         false
% 3.71/1.00  --dbg_dump_prop_clauses                 false
% 3.71/1.00  --dbg_dump_prop_clauses_file            -
% 3.71/1.00  --dbg_out_stat                          false
% 3.71/1.00  ------ Parsing...
% 3.71/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/1.00  ------ Proving...
% 3.71/1.00  ------ Problem Properties 
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  clauses                                 45
% 3.71/1.00  conjectures                             3
% 3.71/1.00  EPR                                     7
% 3.71/1.00  Horn                                    37
% 3.71/1.00  unary                                   9
% 3.71/1.00  binary                                  17
% 3.71/1.00  lits                                    114
% 3.71/1.00  lits eq                                 41
% 3.71/1.00  fd_pure                                 0
% 3.71/1.00  fd_pseudo                               0
% 3.71/1.00  fd_cond                                 2
% 3.71/1.00  fd_pseudo_cond                          1
% 3.71/1.00  AC symbols                              0
% 3.71/1.00  
% 3.71/1.00  ------ Schedule dynamic 5 is on 
% 3.71/1.00  
% 3.71/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  ------ 
% 3.71/1.00  Current options:
% 3.71/1.00  ------ 
% 3.71/1.00  
% 3.71/1.00  ------ Input Options
% 3.71/1.00  
% 3.71/1.00  --out_options                           all
% 3.71/1.00  --tptp_safe_out                         true
% 3.71/1.00  --problem_path                          ""
% 3.71/1.00  --include_path                          ""
% 3.71/1.00  --clausifier                            res/vclausify_rel
% 3.71/1.00  --clausifier_options                    ""
% 3.71/1.00  --stdin                                 false
% 3.71/1.00  --stats_out                             all
% 3.71/1.00  
% 3.71/1.00  ------ General Options
% 3.71/1.00  
% 3.71/1.00  --fof                                   false
% 3.71/1.00  --time_out_real                         305.
% 3.71/1.00  --time_out_virtual                      -1.
% 3.71/1.00  --symbol_type_check                     false
% 3.71/1.00  --clausify_out                          false
% 3.71/1.00  --sig_cnt_out                           false
% 3.71/1.00  --trig_cnt_out                          false
% 3.71/1.00  --trig_cnt_out_tolerance                1.
% 3.71/1.00  --trig_cnt_out_sk_spl                   false
% 3.71/1.00  --abstr_cl_out                          false
% 3.71/1.00  
% 3.71/1.00  ------ Global Options
% 3.71/1.00  
% 3.71/1.00  --schedule                              default
% 3.71/1.00  --add_important_lit                     false
% 3.71/1.00  --prop_solver_per_cl                    1000
% 3.71/1.00  --min_unsat_core                        false
% 3.71/1.00  --soft_assumptions                      false
% 3.71/1.00  --soft_lemma_size                       3
% 3.71/1.00  --prop_impl_unit_size                   0
% 3.71/1.00  --prop_impl_unit                        []
% 3.71/1.00  --share_sel_clauses                     true
% 3.71/1.00  --reset_solvers                         false
% 3.71/1.00  --bc_imp_inh                            [conj_cone]
% 3.71/1.00  --conj_cone_tolerance                   3.
% 3.71/1.00  --extra_neg_conj                        none
% 3.71/1.00  --large_theory_mode                     true
% 3.71/1.00  --prolific_symb_bound                   200
% 3.71/1.00  --lt_threshold                          2000
% 3.71/1.00  --clause_weak_htbl                      true
% 3.71/1.00  --gc_record_bc_elim                     false
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing Options
% 3.71/1.00  
% 3.71/1.00  --preprocessing_flag                    true
% 3.71/1.00  --time_out_prep_mult                    0.1
% 3.71/1.00  --splitting_mode                        input
% 3.71/1.00  --splitting_grd                         true
% 3.71/1.00  --splitting_cvd                         false
% 3.71/1.00  --splitting_cvd_svl                     false
% 3.71/1.00  --splitting_nvd                         32
% 3.71/1.00  --sub_typing                            true
% 3.71/1.00  --prep_gs_sim                           true
% 3.71/1.00  --prep_unflatten                        true
% 3.71/1.00  --prep_res_sim                          true
% 3.71/1.00  --prep_upred                            true
% 3.71/1.00  --prep_sem_filter                       exhaustive
% 3.71/1.00  --prep_sem_filter_out                   false
% 3.71/1.00  --pred_elim                             true
% 3.71/1.00  --res_sim_input                         true
% 3.71/1.00  --eq_ax_congr_red                       true
% 3.71/1.00  --pure_diseq_elim                       true
% 3.71/1.00  --brand_transform                       false
% 3.71/1.00  --non_eq_to_eq                          false
% 3.71/1.00  --prep_def_merge                        true
% 3.71/1.00  --prep_def_merge_prop_impl              false
% 3.71/1.00  --prep_def_merge_mbd                    true
% 3.71/1.00  --prep_def_merge_tr_red                 false
% 3.71/1.00  --prep_def_merge_tr_cl                  false
% 3.71/1.00  --smt_preprocessing                     true
% 3.71/1.00  --smt_ac_axioms                         fast
% 3.71/1.00  --preprocessed_out                      false
% 3.71/1.00  --preprocessed_stats                    false
% 3.71/1.00  
% 3.71/1.00  ------ Abstraction refinement Options
% 3.71/1.00  
% 3.71/1.00  --abstr_ref                             []
% 3.71/1.00  --abstr_ref_prep                        false
% 3.71/1.00  --abstr_ref_until_sat                   false
% 3.71/1.00  --abstr_ref_sig_restrict                funpre
% 3.71/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.00  --abstr_ref_under                       []
% 3.71/1.00  
% 3.71/1.00  ------ SAT Options
% 3.71/1.00  
% 3.71/1.00  --sat_mode                              false
% 3.71/1.00  --sat_fm_restart_options                ""
% 3.71/1.00  --sat_gr_def                            false
% 3.71/1.00  --sat_epr_types                         true
% 3.71/1.00  --sat_non_cyclic_types                  false
% 3.71/1.00  --sat_finite_models                     false
% 3.71/1.00  --sat_fm_lemmas                         false
% 3.71/1.00  --sat_fm_prep                           false
% 3.71/1.00  --sat_fm_uc_incr                        true
% 3.71/1.00  --sat_out_model                         small
% 3.71/1.00  --sat_out_clauses                       false
% 3.71/1.00  
% 3.71/1.00  ------ QBF Options
% 3.71/1.00  
% 3.71/1.00  --qbf_mode                              false
% 3.71/1.00  --qbf_elim_univ                         false
% 3.71/1.00  --qbf_dom_inst                          none
% 3.71/1.00  --qbf_dom_pre_inst                      false
% 3.71/1.00  --qbf_sk_in                             false
% 3.71/1.00  --qbf_pred_elim                         true
% 3.71/1.00  --qbf_split                             512
% 3.71/1.00  
% 3.71/1.00  ------ BMC1 Options
% 3.71/1.00  
% 3.71/1.00  --bmc1_incremental                      false
% 3.71/1.00  --bmc1_axioms                           reachable_all
% 3.71/1.00  --bmc1_min_bound                        0
% 3.71/1.00  --bmc1_max_bound                        -1
% 3.71/1.00  --bmc1_max_bound_default                -1
% 3.71/1.00  --bmc1_symbol_reachability              true
% 3.71/1.00  --bmc1_property_lemmas                  false
% 3.71/1.00  --bmc1_k_induction                      false
% 3.71/1.00  --bmc1_non_equiv_states                 false
% 3.71/1.00  --bmc1_deadlock                         false
% 3.71/1.00  --bmc1_ucm                              false
% 3.71/1.00  --bmc1_add_unsat_core                   none
% 3.71/1.00  --bmc1_unsat_core_children              false
% 3.71/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.00  --bmc1_out_stat                         full
% 3.71/1.00  --bmc1_ground_init                      false
% 3.71/1.00  --bmc1_pre_inst_next_state              false
% 3.71/1.00  --bmc1_pre_inst_state                   false
% 3.71/1.00  --bmc1_pre_inst_reach_state             false
% 3.71/1.00  --bmc1_out_unsat_core                   false
% 3.71/1.00  --bmc1_aig_witness_out                  false
% 3.71/1.00  --bmc1_verbose                          false
% 3.71/1.00  --bmc1_dump_clauses_tptp                false
% 3.71/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.00  --bmc1_dump_file                        -
% 3.71/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.00  --bmc1_ucm_extend_mode                  1
% 3.71/1.00  --bmc1_ucm_init_mode                    2
% 3.71/1.00  --bmc1_ucm_cone_mode                    none
% 3.71/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.00  --bmc1_ucm_relax_model                  4
% 3.71/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.00  --bmc1_ucm_layered_model                none
% 3.71/1.00  --bmc1_ucm_max_lemma_size               10
% 3.71/1.00  
% 3.71/1.00  ------ AIG Options
% 3.71/1.00  
% 3.71/1.00  --aig_mode                              false
% 3.71/1.00  
% 3.71/1.00  ------ Instantiation Options
% 3.71/1.00  
% 3.71/1.00  --instantiation_flag                    true
% 3.71/1.00  --inst_sos_flag                         true
% 3.71/1.00  --inst_sos_phase                        true
% 3.71/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel_side                     none
% 3.71/1.00  --inst_solver_per_active                1400
% 3.71/1.00  --inst_solver_calls_frac                1.
% 3.71/1.00  --inst_passive_queue_type               priority_queues
% 3.71/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.00  --inst_passive_queues_freq              [25;2]
% 3.71/1.00  --inst_dismatching                      true
% 3.71/1.00  --inst_eager_unprocessed_to_passive     true
% 3.71/1.00  --inst_prop_sim_given                   true
% 3.71/1.00  --inst_prop_sim_new                     false
% 3.71/1.00  --inst_subs_new                         false
% 3.71/1.00  --inst_eq_res_simp                      false
% 3.71/1.00  --inst_subs_given                       false
% 3.71/1.00  --inst_orphan_elimination               true
% 3.71/1.00  --inst_learning_loop_flag               true
% 3.71/1.00  --inst_learning_start                   3000
% 3.71/1.00  --inst_learning_factor                  2
% 3.71/1.00  --inst_start_prop_sim_after_learn       3
% 3.71/1.00  --inst_sel_renew                        solver
% 3.71/1.00  --inst_lit_activity_flag                true
% 3.71/1.00  --inst_restr_to_given                   false
% 3.71/1.00  --inst_activity_threshold               500
% 3.71/1.00  --inst_out_proof                        true
% 3.71/1.00  
% 3.71/1.00  ------ Resolution Options
% 3.71/1.00  
% 3.71/1.00  --resolution_flag                       false
% 3.71/1.00  --res_lit_sel                           adaptive
% 3.71/1.00  --res_lit_sel_side                      none
% 3.71/1.00  --res_ordering                          kbo
% 3.71/1.00  --res_to_prop_solver                    active
% 3.71/1.00  --res_prop_simpl_new                    false
% 3.71/1.00  --res_prop_simpl_given                  true
% 3.71/1.00  --res_passive_queue_type                priority_queues
% 3.71/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.00  --res_passive_queues_freq               [15;5]
% 3.71/1.00  --res_forward_subs                      full
% 3.71/1.00  --res_backward_subs                     full
% 3.71/1.00  --res_forward_subs_resolution           true
% 3.71/1.00  --res_backward_subs_resolution          true
% 3.71/1.00  --res_orphan_elimination                true
% 3.71/1.00  --res_time_limit                        2.
% 3.71/1.00  --res_out_proof                         true
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Options
% 3.71/1.00  
% 3.71/1.00  --superposition_flag                    true
% 3.71/1.00  --sup_passive_queue_type                priority_queues
% 3.71/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.71/1.00  --demod_completeness_check              fast
% 3.71/1.00  --demod_use_ground                      true
% 3.71/1.00  --sup_to_prop_solver                    passive
% 3.71/1.00  --sup_prop_simpl_new                    true
% 3.71/1.00  --sup_prop_simpl_given                  true
% 3.71/1.00  --sup_fun_splitting                     true
% 3.71/1.00  --sup_smt_interval                      50000
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Simplification Setup
% 3.71/1.00  
% 3.71/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.71/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.71/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.71/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.71/1.00  --sup_immed_triv                        [TrivRules]
% 3.71/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.00  --sup_immed_bw_main                     []
% 3.71/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.71/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.00  --sup_input_bw                          []
% 3.71/1.00  
% 3.71/1.00  ------ Combination Options
% 3.71/1.00  
% 3.71/1.00  --comb_res_mult                         3
% 3.71/1.00  --comb_sup_mult                         2
% 3.71/1.00  --comb_inst_mult                        10
% 3.71/1.00  
% 3.71/1.00  ------ Debug Options
% 3.71/1.00  
% 3.71/1.00  --dbg_backtrace                         false
% 3.71/1.00  --dbg_dump_prop_clauses                 false
% 3.71/1.00  --dbg_dump_prop_clauses_file            -
% 3.71/1.00  --dbg_out_stat                          false
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  ------ Proving...
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  % SZS status Theorem for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  fof(f4,axiom,(
% 3.71/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f54,plain,(
% 3.71/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.71/1.00    inference(nnf_transformation,[],[f4])).
% 3.71/1.00  
% 3.71/1.00  fof(f55,plain,(
% 3.71/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.71/1.00    inference(flattening,[],[f54])).
% 3.71/1.00  
% 3.71/1.00  fof(f70,plain,(
% 3.71/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f17,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f40,plain,(
% 3.71/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/1.00    inference(ennf_transformation,[],[f17])).
% 3.71/1.00  
% 3.71/1.00  fof(f41,plain,(
% 3.71/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/1.00    inference(flattening,[],[f40])).
% 3.71/1.00  
% 3.71/1.00  fof(f57,plain,(
% 3.71/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/1.00    inference(nnf_transformation,[],[f41])).
% 3.71/1.00  
% 3.71/1.00  fof(f86,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f57])).
% 3.71/1.00  
% 3.71/1.00  fof(f20,conjecture,(
% 3.71/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f21,negated_conjecture,(
% 3.71/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.71/1.00    inference(negated_conjecture,[],[f20])).
% 3.71/1.00  
% 3.71/1.00  fof(f44,plain,(
% 3.71/1.00    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.71/1.00    inference(ennf_transformation,[],[f21])).
% 3.71/1.00  
% 3.71/1.00  fof(f45,plain,(
% 3.71/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.71/1.00    inference(flattening,[],[f44])).
% 3.71/1.00  
% 3.71/1.00  fof(f60,plain,(
% 3.71/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) | ~v1_funct_2(k2_funct_1(sK5),sK4,sK3) | ~v1_funct_1(k2_funct_1(sK5))) & k2_relset_1(sK3,sK4,sK5) = sK4 & v2_funct_1(sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f61,plain,(
% 3.71/1.00    (~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) | ~v1_funct_2(k2_funct_1(sK5),sK4,sK3) | ~v1_funct_1(k2_funct_1(sK5))) & k2_relset_1(sK3,sK4,sK5) = sK4 & v2_funct_1(sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 3.71/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f45,f60])).
% 3.71/1.00  
% 3.71/1.00  fof(f100,plain,(
% 3.71/1.00    v1_funct_2(sK5,sK3,sK4)),
% 3.71/1.00    inference(cnf_transformation,[],[f61])).
% 3.71/1.00  
% 3.71/1.00  fof(f101,plain,(
% 3.71/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.71/1.00    inference(cnf_transformation,[],[f61])).
% 3.71/1.00  
% 3.71/1.00  fof(f15,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f38,plain,(
% 3.71/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/1.00    inference(ennf_transformation,[],[f15])).
% 3.71/1.00  
% 3.71/1.00  fof(f84,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f38])).
% 3.71/1.00  
% 3.71/1.00  fof(f12,axiom,(
% 3.71/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f34,plain,(
% 3.71/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.71/1.00    inference(ennf_transformation,[],[f12])).
% 3.71/1.00  
% 3.71/1.00  fof(f35,plain,(
% 3.71/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.71/1.00    inference(flattening,[],[f34])).
% 3.71/1.00  
% 3.71/1.00  fof(f81,plain,(
% 3.71/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f35])).
% 3.71/1.00  
% 3.71/1.00  fof(f102,plain,(
% 3.71/1.00    v2_funct_1(sK5)),
% 3.71/1.00    inference(cnf_transformation,[],[f61])).
% 3.71/1.00  
% 3.71/1.00  fof(f99,plain,(
% 3.71/1.00    v1_funct_1(sK5)),
% 3.71/1.00    inference(cnf_transformation,[],[f61])).
% 3.71/1.00  
% 3.71/1.00  fof(f13,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f36,plain,(
% 3.71/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/1.00    inference(ennf_transformation,[],[f13])).
% 3.71/1.00  
% 3.71/1.00  fof(f82,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f36])).
% 3.71/1.00  
% 3.71/1.00  fof(f10,axiom,(
% 3.71/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f30,plain,(
% 3.71/1.00    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.71/1.00    inference(ennf_transformation,[],[f10])).
% 3.71/1.00  
% 3.71/1.00  fof(f31,plain,(
% 3.71/1.00    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.71/1.00    inference(flattening,[],[f30])).
% 3.71/1.00  
% 3.71/1.00  fof(f78,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f31])).
% 3.71/1.00  
% 3.71/1.00  fof(f9,axiom,(
% 3.71/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f28,plain,(
% 3.71/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.71/1.00    inference(ennf_transformation,[],[f9])).
% 3.71/1.00  
% 3.71/1.00  fof(f29,plain,(
% 3.71/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.71/1.00    inference(flattening,[],[f28])).
% 3.71/1.00  
% 3.71/1.00  fof(f77,plain,(
% 3.71/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f29])).
% 3.71/1.00  
% 3.71/1.00  fof(f76,plain,(
% 3.71/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f29])).
% 3.71/1.00  
% 3.71/1.00  fof(f19,axiom,(
% 3.71/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f42,plain,(
% 3.71/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.71/1.00    inference(ennf_transformation,[],[f19])).
% 3.71/1.00  
% 3.71/1.00  fof(f43,plain,(
% 3.71/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.71/1.00    inference(flattening,[],[f42])).
% 3.71/1.00  
% 3.71/1.00  fof(f98,plain,(
% 3.71/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f43])).
% 3.71/1.00  
% 3.71/1.00  fof(f16,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f39,plain,(
% 3.71/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/1.00    inference(ennf_transformation,[],[f16])).
% 3.71/1.00  
% 3.71/1.00  fof(f85,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f39])).
% 3.71/1.00  
% 3.71/1.00  fof(f103,plain,(
% 3.71/1.00    k2_relset_1(sK3,sK4,sK5) = sK4),
% 3.71/1.00    inference(cnf_transformation,[],[f61])).
% 3.71/1.00  
% 3.71/1.00  fof(f80,plain,(
% 3.71/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f35])).
% 3.71/1.00  
% 3.71/1.00  fof(f97,plain,(
% 3.71/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f43])).
% 3.71/1.00  
% 3.71/1.00  fof(f104,plain,(
% 3.71/1.00    ~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) | ~v1_funct_2(k2_funct_1(sK5),sK4,sK3) | ~v1_funct_1(k2_funct_1(sK5))),
% 3.71/1.00    inference(cnf_transformation,[],[f61])).
% 3.71/1.00  
% 3.71/1.00  fof(f90,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f57])).
% 3.71/1.00  
% 3.71/1.00  fof(f109,plain,(
% 3.71/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.71/1.00    inference(equality_resolution,[],[f90])).
% 3.71/1.00  
% 3.71/1.00  fof(f5,axiom,(
% 3.71/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f56,plain,(
% 3.71/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.71/1.00    inference(nnf_transformation,[],[f5])).
% 3.71/1.00  
% 3.71/1.00  fof(f72,plain,(
% 3.71/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f56])).
% 3.71/1.00  
% 3.71/1.00  fof(f2,axiom,(
% 3.71/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f24,plain,(
% 3.71/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.71/1.00    inference(ennf_transformation,[],[f2])).
% 3.71/1.00  
% 3.71/1.00  fof(f50,plain,(
% 3.71/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.71/1.00    inference(nnf_transformation,[],[f24])).
% 3.71/1.00  
% 3.71/1.00  fof(f51,plain,(
% 3.71/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.71/1.00    inference(rectify,[],[f50])).
% 3.71/1.00  
% 3.71/1.00  fof(f52,plain,(
% 3.71/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f53,plain,(
% 3.71/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.71/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f51,f52])).
% 3.71/1.00  
% 3.71/1.00  fof(f65,plain,(
% 3.71/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f53])).
% 3.71/1.00  
% 3.71/1.00  fof(f1,axiom,(
% 3.71/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f46,plain,(
% 3.71/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.71/1.00    inference(nnf_transformation,[],[f1])).
% 3.71/1.00  
% 3.71/1.00  fof(f47,plain,(
% 3.71/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.71/1.00    inference(rectify,[],[f46])).
% 3.71/1.00  
% 3.71/1.00  fof(f48,plain,(
% 3.71/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f49,plain,(
% 3.71/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.71/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 3.71/1.00  
% 3.71/1.00  fof(f62,plain,(
% 3.71/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f49])).
% 3.71/1.00  
% 3.71/1.00  fof(f71,plain,(
% 3.71/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f56])).
% 3.71/1.00  
% 3.71/1.00  fof(f14,axiom,(
% 3.71/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f37,plain,(
% 3.71/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f14])).
% 3.71/1.00  
% 3.71/1.00  fof(f83,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f37])).
% 3.71/1.00  
% 3.71/1.00  fof(f3,axiom,(
% 3.71/1.00    v1_xboole_0(k1_xboole_0)),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f67,plain,(
% 3.71/1.00    v1_xboole_0(k1_xboole_0)),
% 3.71/1.00    inference(cnf_transformation,[],[f3])).
% 3.71/1.00  
% 3.71/1.00  fof(f69,plain,(
% 3.71/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f105,plain,(
% 3.71/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.71/1.00    inference(equality_resolution,[],[f69])).
% 3.71/1.00  
% 3.71/1.00  fof(f88,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f57])).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6,plain,
% 3.71/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.71/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4319,plain,
% 3.71/1.00      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | X0 = sK3 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_9963,plain,
% 3.71/1.00      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_4319]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_29,plain,
% 3.71/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.71/1.00      | k1_xboole_0 = X2 ),
% 3.71/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_41,negated_conjecture,
% 3.71/1.00      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.71/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_806,plain,
% 3.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.71/1.00      | sK3 != X1
% 3.71/1.00      | sK4 != X2
% 3.71/1.00      | sK5 != X0
% 3.71/1.00      | k1_xboole_0 = X2 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_41]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_807,plain,
% 3.71/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.71/1.00      | k1_relset_1(sK3,sK4,sK5) = sK3
% 3.71/1.00      | k1_xboole_0 = sK4 ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_806]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_40,negated_conjecture,
% 3.71/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.71/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_809,plain,
% 3.71/1.00      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_807,c_40]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1832,plain,
% 3.71/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_22,plain,
% 3.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1838,plain,
% 3.71/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.71/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3476,plain,
% 3.71/1.00      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_1832,c_1838]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3622,plain,
% 3.71/1.00      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_809,c_3476]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_18,plain,
% 3.71/1.00      ( ~ v2_funct_1(X0)
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | ~ v1_relat_1(X0)
% 3.71/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_39,negated_conjecture,
% 3.71/1.00      ( v2_funct_1(sK5) ),
% 3.71/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_548,plain,
% 3.71/1.00      ( ~ v1_funct_1(X0)
% 3.71/1.00      | ~ v1_relat_1(X0)
% 3.71/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.71/1.00      | sK5 != X0 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_39]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_549,plain,
% 3.71/1.00      ( ~ v1_funct_1(sK5)
% 3.71/1.00      | ~ v1_relat_1(sK5)
% 3.71/1.00      | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_548]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_42,negated_conjecture,
% 3.71/1.00      ( v1_funct_1(sK5) ),
% 3.71/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_551,plain,
% 3.71/1.00      ( ~ v1_relat_1(sK5)
% 3.71/1.00      | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_549,c_42]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1829,plain,
% 3.71/1.00      ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5)
% 3.71/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_551]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_20,plain,
% 3.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | v1_relat_1(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1910,plain,
% 3.71/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/1.00      | v1_relat_1(sK5) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2007,plain,
% 3.71/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.71/1.00      | v1_relat_1(sK5) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_1910]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2070,plain,
% 3.71/1.00      ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_1829,c_42,c_40,c_549,c_2007]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_16,plain,
% 3.71/1.00      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.71/1.00      | ~ v1_funct_1(X1)
% 3.71/1.00      | ~ v1_relat_1(X1)
% 3.71/1.00      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 3.71/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1841,plain,
% 3.71/1.00      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 3.71/1.00      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 3.71/1.00      | v1_funct_1(X0) != iProver_top
% 3.71/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4382,plain,
% 3.71/1.00      ( k9_relat_1(k2_funct_1(sK5),k10_relat_1(k2_funct_1(sK5),X0)) = X0
% 3.71/1.00      | r1_tarski(X0,k1_relat_1(sK5)) != iProver_top
% 3.71/1.00      | v1_funct_1(k2_funct_1(sK5)) != iProver_top
% 3.71/1.00      | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_2070,c_1841]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_43,plain,
% 3.71/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_45,plain,
% 3.71/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_14,plain,
% 3.71/1.00      ( ~ v1_funct_1(X0)
% 3.71/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.71/1.00      | ~ v1_relat_1(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1929,plain,
% 3.71/1.00      ( v1_funct_1(k2_funct_1(sK5))
% 3.71/1.00      | ~ v1_funct_1(sK5)
% 3.71/1.00      | ~ v1_relat_1(sK5) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1930,plain,
% 3.71/1.00      ( v1_funct_1(k2_funct_1(sK5)) = iProver_top
% 3.71/1.00      | v1_funct_1(sK5) != iProver_top
% 3.71/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_1929]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2008,plain,
% 3.71/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.71/1.00      | v1_relat_1(sK5) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_2007]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5051,plain,
% 3.71/1.00      ( r1_tarski(X0,k1_relat_1(sK5)) != iProver_top
% 3.71/1.00      | k9_relat_1(k2_funct_1(sK5),k10_relat_1(k2_funct_1(sK5),X0)) = X0
% 3.71/1.00      | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_4382,c_43,c_45,c_1930,c_2008]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5052,plain,
% 3.71/1.00      ( k9_relat_1(k2_funct_1(sK5),k10_relat_1(k2_funct_1(sK5),X0)) = X0
% 3.71/1.00      | r1_tarski(X0,k1_relat_1(sK5)) != iProver_top
% 3.71/1.00      | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_5051]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5059,plain,
% 3.71/1.00      ( k9_relat_1(k2_funct_1(sK5),k10_relat_1(k2_funct_1(sK5),X0)) = X0
% 3.71/1.00      | sK4 = k1_xboole_0
% 3.71/1.00      | r1_tarski(X0,sK3) != iProver_top
% 3.71/1.00      | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_3622,c_5052]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_15,plain,
% 3.71/1.00      ( ~ v1_funct_1(X0)
% 3.71/1.00      | ~ v1_relat_1(X0)
% 3.71/1.00      | v1_relat_1(k2_funct_1(X0)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1842,plain,
% 3.71/1.00      ( v1_funct_1(X0) != iProver_top
% 3.71/1.00      | v1_relat_1(X0) != iProver_top
% 3.71/1.00      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_34,plain,
% 3.71/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | ~ v1_relat_1(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1833,plain,
% 3.71/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.71/1.00      | v1_funct_1(X0) != iProver_top
% 3.71/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3830,plain,
% 3.71/1.00      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK5)),k1_relat_1(sK5)))) = iProver_top
% 3.71/1.00      | v1_funct_1(k2_funct_1(sK5)) != iProver_top
% 3.71/1.00      | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_2070,c_1833]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_23,plain,
% 3.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1837,plain,
% 3.71/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.71/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3430,plain,
% 3.71/1.00      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_1832,c_1837]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_38,negated_conjecture,
% 3.71/1.00      ( k2_relset_1(sK3,sK4,sK5) = sK4 ),
% 3.71/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3431,plain,
% 3.71/1.00      ( k2_relat_1(sK5) = sK4 ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_3430,c_38]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_19,plain,
% 3.71/1.00      ( ~ v2_funct_1(X0)
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | ~ v1_relat_1(X0)
% 3.71/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_534,plain,
% 3.71/1.00      ( ~ v1_funct_1(X0)
% 3.71/1.00      | ~ v1_relat_1(X0)
% 3.71/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.71/1.00      | sK5 != X0 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_39]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_535,plain,
% 3.71/1.00      ( ~ v1_funct_1(sK5)
% 3.71/1.00      | ~ v1_relat_1(sK5)
% 3.71/1.00      | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_534]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_537,plain,
% 3.71/1.00      ( ~ v1_relat_1(sK5)
% 3.71/1.00      | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_535,c_42]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1830,plain,
% 3.71/1.00      ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5)
% 3.71/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2073,plain,
% 3.71/1.00      ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_1830,c_42,c_40,c_535,c_2007]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3467,plain,
% 3.71/1.00      ( k1_relat_1(k2_funct_1(sK5)) = sK4 ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_3431,c_2073]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3835,plain,
% 3.71/1.00      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k1_relat_1(sK5)))) = iProver_top
% 3.71/1.00      | v1_funct_1(k2_funct_1(sK5)) != iProver_top
% 3.71/1.00      | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_3830,c_3467]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4824,plain,
% 3.71/1.00      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k1_relat_1(sK5)))) = iProver_top
% 3.71/1.00      | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_3835,c_43,c_45,c_1930,c_2008]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4828,plain,
% 3.71/1.00      ( sK4 = k1_xboole_0
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top
% 3.71/1.00      | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_3622,c_4824]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_35,plain,
% 3.71/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | ~ v1_relat_1(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_37,negated_conjecture,
% 3.71/1.00      ( ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
% 3.71/1.00      | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.71/1.00      | ~ v1_funct_1(k2_funct_1(sK5)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_830,plain,
% 3.71/1.00      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.71/1.00      | ~ v1_relat_1(X0)
% 3.71/1.00      | k2_funct_1(sK5) != X0
% 3.71/1.00      | k2_relat_1(X0) != sK3
% 3.71/1.00      | k1_relat_1(X0) != sK4 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_35,c_37]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_831,plain,
% 3.71/1.00      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.71/1.00      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.71/1.00      | ~ v1_relat_1(k2_funct_1(sK5))
% 3.71/1.00      | k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.71/1.00      | k1_relat_1(k2_funct_1(sK5)) != sK4 ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_830]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_843,plain,
% 3.71/1.00      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.71/1.00      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.71/1.00      | k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.71/1.00      | k1_relat_1(k2_funct_1(sK5)) != sK4 ),
% 3.71/1.00      inference(forward_subsumption_resolution,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_831,c_20]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1818,plain,
% 3.71/1.00      ( k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.71/1.00      | k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.71/1.00      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_843]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_848,plain,
% 3.71/1.00      ( k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.71/1.00      | k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.71/1.00      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_843]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2336,plain,
% 3.71/1.00      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.71/1.00      | k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.71/1.00      | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_1818,c_43,c_45,c_848,c_1930,c_2008]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2337,plain,
% 3.71/1.00      ( k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.71/1.00      | k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_2336]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2340,plain,
% 3.71/1.00      ( k2_relat_1(sK5) != sK4
% 3.71/1.00      | k1_relat_1(sK5) != sK3
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_2337,c_2070,c_2073]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3466,plain,
% 3.71/1.00      ( k1_relat_1(sK5) != sK3
% 3.71/1.00      | sK4 != sK4
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_3431,c_2340]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3468,plain,
% 3.71/1.00      ( k1_relat_1(sK5) != sK3
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.71/1.00      inference(equality_resolution_simp,[status(thm)],[c_3466]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4721,plain,
% 3.71/1.00      ( sK4 = k1_xboole_0
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_3622,c_3468]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5184,plain,
% 3.71/1.00      ( sK4 = k1_xboole_0 | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_4828,c_4721]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5188,plain,
% 3.71/1.00      ( sK4 = k1_xboole_0
% 3.71/1.00      | v1_funct_1(sK5) != iProver_top
% 3.71/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_1842,c_5184]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5191,plain,
% 3.71/1.00      ( sK4 = k1_xboole_0 ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_5059,c_43,c_45,c_2008,c_5188]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_25,plain,
% 3.71/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.71/1.00      | k1_xboole_0 = X1
% 3.71/1.00      | k1_xboole_0 = X0 ),
% 3.71/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_668,plain,
% 3.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.71/1.00      | sK3 != X1
% 3.71/1.00      | sK4 != k1_xboole_0
% 3.71/1.00      | sK5 != X0
% 3.71/1.00      | k1_xboole_0 = X0
% 3.71/1.00      | k1_xboole_0 = X1 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_41]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_669,plain,
% 3.71/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
% 3.71/1.00      | sK4 != k1_xboole_0
% 3.71/1.00      | k1_xboole_0 = sK3
% 3.71/1.00      | k1_xboole_0 = sK5 ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_668]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1825,plain,
% 3.71/1.00      ( sK4 != k1_xboole_0
% 3.71/1.00      | k1_xboole_0 = sK3
% 3.71/1.00      | k1_xboole_0 = sK5
% 3.71/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5215,plain,
% 3.71/1.00      ( sK3 = k1_xboole_0
% 3.71/1.00      | sK5 = k1_xboole_0
% 3.71/1.00      | k1_xboole_0 != k1_xboole_0
% 3.71/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_5191,c_1825]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5226,plain,
% 3.71/1.00      ( sK3 = k1_xboole_0
% 3.71/1.00      | sK5 = k1_xboole_0
% 3.71/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
% 3.71/1.00      inference(equality_resolution_simp,[status(thm)],[c_5215]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_9,plain,
% 3.71/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2044,plain,
% 3.71/1.00      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.71/1.00      | ~ r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2045,plain,
% 3.71/1.00      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top
% 3.71/1.00      | r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_2044]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3,plain,
% 3.71/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2154,plain,
% 3.71/1.00      ( r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3))
% 3.71/1.00      | r2_hidden(sK1(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)),k2_funct_1(sK5)) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2158,plain,
% 3.71/1.00      ( r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)) = iProver_top
% 3.71/1.00      | r2_hidden(sK1(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)),k2_funct_1(sK5)) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_2154]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_930,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2057,plain,
% 3.71/1.00      ( k2_relat_1(k2_funct_1(sK5)) != X0
% 3.71/1.00      | k2_relat_1(k2_funct_1(sK5)) = sK3
% 3.71/1.00      | sK3 != X0 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_930]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2280,plain,
% 3.71/1.00      ( k2_relat_1(k2_funct_1(sK5)) != k1_relat_1(sK5)
% 3.71/1.00      | k2_relat_1(k2_funct_1(sK5)) = sK3
% 3.71/1.00      | sK3 != k1_relat_1(sK5) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_2057]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2064,plain,
% 3.71/1.00      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_930]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2384,plain,
% 3.71/1.00      ( k1_relat_1(sK5) != X0 | sK3 != X0 | sK3 = k1_relat_1(sK5) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_2064]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2388,plain,
% 3.71/1.00      ( k1_relat_1(sK5) != k1_xboole_0
% 3.71/1.00      | sK3 = k1_relat_1(sK5)
% 3.71/1.00      | sK3 != k1_xboole_0 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_2384]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2010,plain,
% 3.71/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/1.00      | ~ r1_tarski(sK5,k2_zfmisc_1(X0,X1)) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2881,plain,
% 3.71/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
% 3.71/1.00      | ~ r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_2010]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2882,plain,
% 3.71/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top
% 3.71/1.00      | r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_2881]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_642,plain,
% 3.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.71/1.00      | ~ v1_funct_1(X2)
% 3.71/1.00      | ~ v1_relat_1(X2)
% 3.71/1.00      | X2 != X0
% 3.71/1.00      | k2_relat_1(X2) != k1_xboole_0
% 3.71/1.00      | k1_relat_1(X2) != X1
% 3.71/1.00      | k1_xboole_0 = X0
% 3.71/1.00      | k1_xboole_0 = X1 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_35]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_643,plain,
% 3.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | ~ v1_relat_1(X0)
% 3.71/1.00      | k2_relat_1(X0) != k1_xboole_0
% 3.71/1.00      | k1_xboole_0 = X0
% 3.71/1.00      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_642]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_659,plain,
% 3.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | k2_relat_1(X0) != k1_xboole_0
% 3.71/1.00      | k1_xboole_0 = X0
% 3.71/1.00      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.71/1.00      inference(forward_subsumption_resolution,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_643,c_20]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1826,plain,
% 3.71/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 3.71/1.00      | k1_xboole_0 = X0
% 3.71/1.00      | k1_xboole_0 = k1_relat_1(X0)
% 3.71/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
% 3.71/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3471,plain,
% 3.71/1.00      ( k1_relat_1(sK5) = k1_xboole_0
% 3.71/1.00      | sK4 != k1_xboole_0
% 3.71/1.00      | sK5 = k1_xboole_0
% 3.71/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k1_xboole_0))) != iProver_top
% 3.71/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_3431,c_1826]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4155,plain,
% 3.71/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k1_xboole_0))) != iProver_top
% 3.71/1.00      | sK5 = k1_xboole_0
% 3.71/1.00      | sK4 != k1_xboole_0
% 3.71/1.00      | k1_relat_1(sK5) = k1_xboole_0 ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_3471,c_43]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4156,plain,
% 3.71/1.00      ( k1_relat_1(sK5) = k1_xboole_0
% 3.71/1.00      | sK4 != k1_xboole_0
% 3.71/1.00      | sK5 = k1_xboole_0
% 3.71/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k1_xboole_0))) != iProver_top ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_4155]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1,plain,
% 3.71/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2089,plain,
% 3.71/1.00      ( ~ r2_hidden(X0,k2_funct_1(sK5))
% 3.71/1.00      | ~ v1_xboole_0(k2_funct_1(sK5)) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4973,plain,
% 3.71/1.00      ( ~ r2_hidden(sK1(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)),k2_funct_1(sK5))
% 3.71/1.00      | ~ v1_xboole_0(k2_funct_1(sK5)) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_2089]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4974,plain,
% 3.71/1.00      ( r2_hidden(sK1(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)),k2_funct_1(sK5)) != iProver_top
% 3.71/1.00      | v1_xboole_0(k2_funct_1(sK5)) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_4973]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3829,plain,
% 3.71/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top
% 3.71/1.00      | v1_funct_1(sK5) != iProver_top
% 3.71/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_3431,c_1833]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4096,plain,
% 3.71/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) = iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_3829,c_43,c_45,c_2008]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5206,plain,
% 3.71/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k1_xboole_0))) = iProver_top ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_5191,c_4096]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_10,plain,
% 3.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1847,plain,
% 3.71/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.71/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2827,plain,
% 3.71/1.00      ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_1832,c_1847]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5214,plain,
% 3.71/1.00      ( r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) = iProver_top ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_5191,c_2827]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_21,plain,
% 3.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | ~ v1_xboole_0(X1)
% 3.71/1.00      | v1_xboole_0(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1839,plain,
% 3.71/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.71/1.00      | v1_xboole_0(X1) != iProver_top
% 3.71/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4830,plain,
% 3.71/1.00      ( v1_relat_1(k2_funct_1(sK5)) != iProver_top
% 3.71/1.00      | v1_xboole_0(k2_funct_1(sK5)) = iProver_top
% 3.71/1.00      | v1_xboole_0(sK4) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_4824,c_1839]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5,plain,
% 3.71/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_135,plain,
% 3.71/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_931,plain,
% 3.71/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.71/1.00      theory(equality) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6010,plain,
% 3.71/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_931]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6011,plain,
% 3.71/1.00      ( sK4 != X0
% 3.71/1.00      | v1_xboole_0(X0) != iProver_top
% 3.71/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_6010]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6013,plain,
% 3.71/1.00      ( sK4 != k1_xboole_0
% 3.71/1.00      | v1_xboole_0(sK4) = iProver_top
% 3.71/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_6011]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6475,plain,
% 3.71/1.00      ( v1_xboole_0(k2_funct_1(sK5)) = iProver_top
% 3.71/1.00      | v1_relat_1(k2_funct_1(sK5)) != iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_4830,c_43,c_45,c_135,c_2008,c_5188,c_6013]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6476,plain,
% 3.71/1.00      ( v1_relat_1(k2_funct_1(sK5)) != iProver_top
% 3.71/1.00      | v1_xboole_0(k2_funct_1(sK5)) = iProver_top ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_6475]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6479,plain,
% 3.71/1.00      ( v1_funct_1(sK5) != iProver_top
% 3.71/1.00      | v1_relat_1(sK5) != iProver_top
% 3.71/1.00      | v1_xboole_0(k2_funct_1(sK5)) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_1842,c_6476]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_7488,plain,
% 3.71/1.00      ( sK5 = k1_xboole_0 ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_5226,c_42,c_43,c_40,c_45,c_549,c_848,c_1930,c_2007,
% 3.71/1.00                 c_2008,c_2045,c_2158,c_2280,c_2388,c_2882,c_3467,c_4156,
% 3.71/1.00                 c_4974,c_5188,c_5206,c_5214,c_6479]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_7436,plain,
% 3.71/1.00      ( ~ r2_hidden(sK1(X0,k2_funct_1(sK5)),X0) | ~ v1_xboole_0(X0) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_7438,plain,
% 3.71/1.00      ( ~ r2_hidden(sK1(k1_xboole_0,k2_funct_1(sK5)),k1_xboole_0)
% 3.71/1.00      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_7436]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6594,plain,
% 3.71/1.00      ( ~ r2_hidden(sK1(k2_funct_1(sK5),X0),k2_funct_1(sK5))
% 3.71/1.00      | ~ v1_xboole_0(k2_funct_1(sK5)) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_2089]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6596,plain,
% 3.71/1.00      ( ~ r2_hidden(sK1(k2_funct_1(sK5),k1_xboole_0),k2_funct_1(sK5))
% 3.71/1.00      | ~ v1_xboole_0(k2_funct_1(sK5)) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_6594]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6495,plain,
% 3.71/1.00      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.71/1.00      | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) = k1_relat_1(k2_funct_1(sK5)) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6480,plain,
% 3.71/1.00      ( ~ v1_funct_1(sK5)
% 3.71/1.00      | ~ v1_relat_1(sK5)
% 3.71/1.00      | v1_xboole_0(k2_funct_1(sK5)) ),
% 3.71/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6479]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_849,plain,
% 3.71/1.00      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.71/1.00      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.71/1.00      | k2_funct_1(sK5) != sK5
% 3.71/1.00      | sK3 != sK4 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_37,c_41]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1817,plain,
% 3.71/1.00      ( k2_funct_1(sK5) != sK5
% 3.71/1.00      | sK3 != sK4
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.71/1.00      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_850,plain,
% 3.71/1.00      ( k2_funct_1(sK5) != sK5
% 3.71/1.00      | sK3 != sK4
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.71/1.00      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2143,plain,
% 3.71/1.00      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.71/1.00      | sK3 != sK4
% 3.71/1.00      | k2_funct_1(sK5) != sK5 ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_1817,c_43,c_45,c_850,c_1930,c_2008]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2144,plain,
% 3.71/1.00      ( k2_funct_1(sK5) != sK5
% 3.71/1.00      | sK3 != sK4
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_2143]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5220,plain,
% 3.71/1.00      ( k2_funct_1(sK5) != sK5
% 3.71/1.00      | sK3 != k1_xboole_0
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_5191,c_2144]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2052,plain,
% 3.71/1.00      ( sK3 != X0 | sK3 = sK4 | sK4 != X0 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_930]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2053,plain,
% 3.71/1.00      ( sK3 = sK4 | sK3 != k1_xboole_0 | sK4 != k1_xboole_0 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_2052]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2145,plain,
% 3.71/1.00      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.71/1.00      | k2_funct_1(sK5) != sK5
% 3.71/1.00      | sK3 != sK4 ),
% 3.71/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2144]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_939,plain,
% 3.71/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 3.71/1.00      theory(equality) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2202,plain,
% 3.71/1.00      ( v1_relat_1(X0) | ~ v1_relat_1(sK5) | X0 != sK5 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_939]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3817,plain,
% 3.71/1.00      ( v1_relat_1(k2_funct_1(sK5))
% 3.71/1.00      | ~ v1_relat_1(sK5)
% 3.71/1.00      | k2_funct_1(sK5) != sK5 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_2202]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4838,plain,
% 3.71/1.00      ( ~ v1_relat_1(k2_funct_1(sK5))
% 3.71/1.00      | v1_xboole_0(k2_funct_1(sK5))
% 3.71/1.00      | ~ v1_xboole_0(sK4) ),
% 3.71/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4830]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6012,plain,
% 3.71/1.00      ( v1_xboole_0(sK4)
% 3.71/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 3.71/1.00      | sK4 != k1_xboole_0 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_6010]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6016,plain,
% 3.71/1.00      ( sK3 != k1_xboole_0 | k2_funct_1(sK5) != sK5 ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_5220,c_43,c_40,c_45,c_5,c_2007,c_2008,c_2044,c_2053,
% 3.71/1.00                 c_2145,c_2154,c_3817,c_4838,c_4973,c_5188,c_6012]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6017,plain,
% 3.71/1.00      ( k2_funct_1(sK5) != sK5 | sK3 != k1_xboole_0 ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_6016]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_7,plain,
% 3.71/1.00      ( r1_tarski(X0,X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5536,plain,
% 3.71/1.00      ( r1_tarski(sK3,sK3) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2037,plain,
% 3.71/1.00      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_930]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2664,plain,
% 3.71/1.00      ( k1_relat_1(k2_funct_1(sK5)) != X0
% 3.71/1.00      | sK4 != X0
% 3.71/1.00      | sK4 = k1_relat_1(k2_funct_1(sK5)) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_2037]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4170,plain,
% 3.71/1.00      ( k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.71/1.00      | sK4 = k1_relat_1(k2_funct_1(sK5))
% 3.71/1.00      | sK4 != sK4 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_2664]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_929,plain,( X0 = X0 ),theory(equality) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3449,plain,
% 3.71/1.00      ( sK4 = sK4 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_929]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3262,plain,
% 3.71/1.00      ( r1_tarski(k2_funct_1(sK5),X0)
% 3.71/1.00      | r2_hidden(sK1(k2_funct_1(sK5),X0),k2_funct_1(sK5)) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3269,plain,
% 3.71/1.00      ( r1_tarski(k2_funct_1(sK5),k1_xboole_0)
% 3.71/1.00      | r2_hidden(sK1(k2_funct_1(sK5),k1_xboole_0),k2_funct_1(sK5)) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_3262]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2766,plain,
% 3.71/1.00      ( r1_tarski(X0,k2_funct_1(sK5))
% 3.71/1.00      | r2_hidden(sK1(X0,k2_funct_1(sK5)),X0) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2773,plain,
% 3.71/1.00      ( r1_tarski(k1_xboole_0,k2_funct_1(sK5))
% 3.71/1.00      | r2_hidden(sK1(k1_xboole_0,k2_funct_1(sK5)),k1_xboole_0) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_2766]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2444,plain,
% 3.71/1.00      ( ~ r1_tarski(X0,k2_funct_1(sK5))
% 3.71/1.00      | ~ r1_tarski(k2_funct_1(sK5),X0)
% 3.71/1.00      | k2_funct_1(sK5) = X0 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2446,plain,
% 3.71/1.00      ( ~ r1_tarski(k2_funct_1(sK5),k1_xboole_0)
% 3.71/1.00      | ~ r1_tarski(k1_xboole_0,k2_funct_1(sK5))
% 3.71/1.00      | k2_funct_1(sK5) = k1_xboole_0 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_2444]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2228,plain,
% 3.71/1.00      ( k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != X0
% 3.71/1.00      | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) = sK4
% 3.71/1.00      | sK4 != X0 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_930]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2439,plain,
% 3.71/1.00      ( k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != k1_relat_1(k2_funct_1(sK5))
% 3.71/1.00      | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) = sK4
% 3.71/1.00      | sK4 != k1_relat_1(k2_funct_1(sK5)) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_2228]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2171,plain,
% 3.71/1.00      ( k2_funct_1(sK5) != X0 | k2_funct_1(sK5) = sK5 | sK5 != X0 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_930]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2172,plain,
% 3.71/1.00      ( k2_funct_1(sK5) = sK5
% 3.71/1.00      | k2_funct_1(sK5) != k1_xboole_0
% 3.71/1.00      | sK5 != k1_xboole_0 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_2171]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1937,plain,
% 3.71/1.00      ( sK3 != X0 | sK3 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_930]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2068,plain,
% 3.71/1.00      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_1937]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_27,plain,
% 3.71/1.00      ( v1_funct_2(X0,X1,X2)
% 3.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.71/1.00      | k1_xboole_0 = X2 ),
% 3.71/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_790,plain,
% 3.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.71/1.00      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.71/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.71/1.00      | k2_funct_1(sK5) != X0
% 3.71/1.00      | sK3 != X2
% 3.71/1.00      | sK4 != X1
% 3.71/1.00      | k1_xboole_0 = X2 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_37]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_791,plain,
% 3.71/1.00      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.71/1.00      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.71/1.00      | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != sK4
% 3.71/1.00      | k1_xboole_0 = sK3 ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_790]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_792,plain,
% 3.71/1.00      ( k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != sK4
% 3.71/1.00      | k1_xboole_0 = sK3
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.71/1.00      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(contradiction,plain,
% 3.71/1.00      ( $false ),
% 3.71/1.00      inference(minisat,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_9963,c_7488,c_7438,c_6596,c_6495,c_6480,c_6479,c_6017,
% 3.71/1.00                 c_5536,c_4974,c_4973,c_4170,c_3467,c_3449,c_3269,c_2773,
% 3.71/1.00                 c_2446,c_2439,c_2172,c_2158,c_2154,c_2068,c_2045,c_2044,
% 3.71/1.00                 c_2008,c_2007,c_1930,c_792,c_5,c_45,c_40,c_43,c_42]) ).
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  ------                               Statistics
% 3.71/1.00  
% 3.71/1.00  ------ General
% 3.71/1.00  
% 3.71/1.00  abstr_ref_over_cycles:                  0
% 3.71/1.00  abstr_ref_under_cycles:                 0
% 3.71/1.00  gc_basic_clause_elim:                   0
% 3.71/1.00  forced_gc_time:                         0
% 3.71/1.00  parsing_time:                           0.014
% 3.71/1.00  unif_index_cands_time:                  0.
% 3.71/1.00  unif_index_add_time:                    0.
% 3.71/1.00  orderings_time:                         0.
% 3.71/1.00  out_proof_time:                         0.016
% 3.71/1.00  total_time:                             0.296
% 3.71/1.00  num_of_symbols:                         55
% 3.71/1.00  num_of_terms:                           7783
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing
% 3.71/1.00  
% 3.71/1.00  num_of_splits:                          0
% 3.71/1.00  num_of_split_atoms:                     0
% 3.71/1.00  num_of_reused_defs:                     0
% 3.71/1.00  num_eq_ax_congr_red:                    16
% 3.71/1.00  num_of_sem_filtered_clauses:            1
% 3.71/1.00  num_of_subtypes:                        0
% 3.71/1.00  monotx_restored_types:                  0
% 3.71/1.00  sat_num_of_epr_types:                   0
% 3.71/1.00  sat_num_of_non_cyclic_types:            0
% 3.71/1.00  sat_guarded_non_collapsed_types:        0
% 3.71/1.00  num_pure_diseq_elim:                    0
% 3.71/1.00  simp_replaced_by:                       0
% 3.71/1.00  res_preprocessed:                       168
% 3.71/1.00  prep_upred:                             0
% 3.71/1.00  prep_unflattend:                        55
% 3.71/1.00  smt_new_axioms:                         0
% 3.71/1.00  pred_elim_cands:                        8
% 3.71/1.00  pred_elim:                              2
% 3.71/1.00  pred_elim_cl:                           -4
% 3.71/1.00  pred_elim_cycles:                       3
% 3.71/1.00  merged_defs:                            6
% 3.71/1.00  merged_defs_ncl:                        0
% 3.71/1.00  bin_hyper_res:                          6
% 3.71/1.00  prep_cycles:                            3
% 3.71/1.00  pred_elim_time:                         0.009
% 3.71/1.00  splitting_time:                         0.
% 3.71/1.00  sem_filter_time:                        0.
% 3.71/1.00  monotx_time:                            0.
% 3.71/1.00  subtype_inf_time:                       0.
% 3.71/1.00  
% 3.71/1.00  ------ Problem properties
% 3.71/1.00  
% 3.71/1.00  clauses:                                45
% 3.71/1.00  conjectures:                            3
% 3.71/1.00  epr:                                    7
% 3.71/1.00  horn:                                   37
% 3.71/1.00  ground:                                 15
% 3.71/1.00  unary:                                  9
% 3.71/1.00  binary:                                 17
% 3.71/1.00  lits:                                   114
% 3.71/1.00  lits_eq:                                41
% 3.71/1.00  fd_pure:                                0
% 3.71/1.00  fd_pseudo:                              0
% 3.71/1.00  fd_cond:                                2
% 3.71/1.00  fd_pseudo_cond:                         1
% 3.71/1.00  ac_symbols:                             0
% 3.71/1.00  
% 3.71/1.00  ------ Propositional Solver
% 3.71/1.00  
% 3.71/1.00  prop_solver_calls:                      29
% 3.71/1.00  prop_fast_solver_calls:                 1392
% 3.71/1.00  smt_solver_calls:                       0
% 3.71/1.00  smt_fast_solver_calls:                  0
% 3.71/1.00  prop_num_of_clauses:                    4100
% 3.71/1.00  prop_preprocess_simplified:             10371
% 3.71/1.00  prop_fo_subsumed:                       51
% 3.71/1.00  prop_solver_time:                       0.
% 3.71/1.00  smt_solver_time:                        0.
% 3.71/1.00  smt_fast_solver_time:                   0.
% 3.71/1.00  prop_fast_solver_time:                  0.
% 3.71/1.00  prop_unsat_core_time:                   0.
% 3.71/1.00  
% 3.71/1.00  ------ QBF
% 3.71/1.00  
% 3.71/1.00  qbf_q_res:                              0
% 3.71/1.00  qbf_num_tautologies:                    0
% 3.71/1.00  qbf_prep_cycles:                        0
% 3.71/1.00  
% 3.71/1.00  ------ BMC1
% 3.71/1.00  
% 3.71/1.00  bmc1_current_bound:                     -1
% 3.71/1.00  bmc1_last_solved_bound:                 -1
% 3.71/1.00  bmc1_unsat_core_size:                   -1
% 3.71/1.00  bmc1_unsat_core_parents_size:           -1
% 3.71/1.00  bmc1_merge_next_fun:                    0
% 3.71/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.71/1.00  
% 3.71/1.00  ------ Instantiation
% 3.71/1.00  
% 3.71/1.00  inst_num_of_clauses:                    1320
% 3.71/1.00  inst_num_in_passive:                    689
% 3.71/1.00  inst_num_in_active:                     588
% 3.71/1.00  inst_num_in_unprocessed:                42
% 3.71/1.00  inst_num_of_loops:                      906
% 3.71/1.00  inst_num_of_learning_restarts:          0
% 3.71/1.00  inst_num_moves_active_passive:          312
% 3.71/1.00  inst_lit_activity:                      0
% 3.71/1.00  inst_lit_activity_moves:                0
% 3.71/1.00  inst_num_tautologies:                   0
% 3.71/1.00  inst_num_prop_implied:                  0
% 3.71/1.00  inst_num_existing_simplified:           0
% 3.71/1.00  inst_num_eq_res_simplified:             0
% 3.71/1.00  inst_num_child_elim:                    0
% 3.71/1.00  inst_num_of_dismatching_blockings:      292
% 3.71/1.00  inst_num_of_non_proper_insts:           1296
% 3.71/1.00  inst_num_of_duplicates:                 0
% 3.71/1.00  inst_inst_num_from_inst_to_res:         0
% 3.71/1.00  inst_dismatching_checking_time:         0.
% 3.71/1.00  
% 3.71/1.00  ------ Resolution
% 3.71/1.00  
% 3.71/1.00  res_num_of_clauses:                     0
% 3.71/1.00  res_num_in_passive:                     0
% 3.71/1.00  res_num_in_active:                      0
% 3.71/1.00  res_num_of_loops:                       171
% 3.71/1.00  res_forward_subset_subsumed:            54
% 3.71/1.00  res_backward_subset_subsumed:           4
% 3.71/1.00  res_forward_subsumed:                   0
% 3.71/1.00  res_backward_subsumed:                  0
% 3.71/1.00  res_forward_subsumption_resolution:     5
% 3.71/1.00  res_backward_subsumption_resolution:    0
% 3.71/1.00  res_clause_to_clause_subsumption:       535
% 3.71/1.00  res_orphan_elimination:                 0
% 3.71/1.00  res_tautology_del:                      118
% 3.71/1.00  res_num_eq_res_simplified:              0
% 3.71/1.00  res_num_sel_changes:                    0
% 3.71/1.00  res_moves_from_active_to_pass:          0
% 3.71/1.00  
% 3.71/1.00  ------ Superposition
% 3.71/1.00  
% 3.71/1.00  sup_time_total:                         0.
% 3.71/1.00  sup_time_generating:                    0.
% 3.71/1.00  sup_time_sim_full:                      0.
% 3.71/1.00  sup_time_sim_immed:                     0.
% 3.71/1.00  
% 3.71/1.00  sup_num_of_clauses:                     173
% 3.71/1.00  sup_num_in_active:                      83
% 3.71/1.00  sup_num_in_passive:                     90
% 3.71/1.00  sup_num_of_loops:                       180
% 3.71/1.00  sup_fw_superposition:                   144
% 3.71/1.00  sup_bw_superposition:                   135
% 3.71/1.00  sup_immediate_simplified:               59
% 3.71/1.00  sup_given_eliminated:                   0
% 3.71/1.00  comparisons_done:                       0
% 3.71/1.00  comparisons_avoided:                    20
% 3.71/1.00  
% 3.71/1.00  ------ Simplifications
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  sim_fw_subset_subsumed:                 19
% 3.71/1.00  sim_bw_subset_subsumed:                 11
% 3.71/1.00  sim_fw_subsumed:                        4
% 3.71/1.00  sim_bw_subsumed:                        4
% 3.71/1.00  sim_fw_subsumption_res:                 0
% 3.71/1.00  sim_bw_subsumption_res:                 0
% 3.71/1.00  sim_tautology_del:                      8
% 3.71/1.00  sim_eq_tautology_del:                   23
% 3.71/1.00  sim_eq_res_simp:                        5
% 3.71/1.00  sim_fw_demodulated:                     1
% 3.71/1.00  sim_bw_demodulated:                     89
% 3.71/1.00  sim_light_normalised:                   50
% 3.71/1.00  sim_joinable_taut:                      0
% 3.71/1.00  sim_joinable_simp:                      0
% 3.71/1.00  sim_ac_normalised:                      0
% 3.71/1.00  sim_smt_subsumption:                    0
% 3.71/1.00  
%------------------------------------------------------------------------------
