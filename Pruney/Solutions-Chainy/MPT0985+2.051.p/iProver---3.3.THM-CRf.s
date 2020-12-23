%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:30 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  231 (1386 expanded)
%              Number of clauses        :  136 ( 461 expanded)
%              Number of leaves         :   28 ( 272 expanded)
%              Depth                    :   18
%              Number of atoms          :  689 (6787 expanded)
%              Number of equality atoms :  258 (1328 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,axiom,(
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

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f69])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f33,conjecture,(
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

fof(f34,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f71,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f72,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f71])).

fof(f81,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & k2_relset_1(sK1,sK2,sK3) = sK2
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f72,f81])).

fof(f139,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f113,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f136,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

fof(f138,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f82])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f31,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f68,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f67])).

fof(f129,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f112,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f140,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f82])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f106,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f105,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f63])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f141,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f82])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f98,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f29,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f125,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f102,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f30,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f126,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f142,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f102,f126])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 != X0
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f152,plain,(
    ! [X2,X3,X1] :
      ( v1_funct_2(X3,k1_xboole_0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f133])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f65])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f124,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f108,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f146,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f108,f126])).

fof(f14,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f104,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f145,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f104,f126])).

fof(f128,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f80,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f100,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f73])).

fof(f75,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f74,f75])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_49,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_8290,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X0,X1,k1_relat_1(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_relat_1(sK3))))
    | ~ r1_tarski(k1_relat_1(sK3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_18045,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
    | ~ r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8290])).

cnf(c_54,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_4618,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_29,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_4632,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_10413,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4618,c_4632])).

cnf(c_57,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_55,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_858,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_54])).

cnf(c_859,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_858])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_5062,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_11230,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10413,c_57,c_55,c_859,c_5062])).

cnf(c_43,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_4625,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_11233,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11230,c_4625])).

cnf(c_30,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_4631,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_9593,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4618,c_4631])).

cnf(c_4617,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_4628,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_7932,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4617,c_4628])).

cnf(c_53,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_7938,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_7932,c_53])).

cnf(c_9594,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9593,c_7938])).

cnf(c_58,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_60,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_5063,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5062])).

cnf(c_9667,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9594,c_58,c_60,c_5063])).

cnf(c_11260,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11233,c_9667])).

cnf(c_22,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_5020,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_5021,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5020])).

cnf(c_23,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_5028,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_5029,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5028])).

cnf(c_14591,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11260,c_58,c_60,c_5021,c_5029,c_5063])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_4627,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_14597,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14591,c_4627])).

cnf(c_14635,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14597,c_11230])).

cnf(c_52,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_4619,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_62,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_5068,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4619,c_58,c_60,c_62,c_5021,c_5063])).

cnf(c_5069,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5068])).

cnf(c_14758,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_14635,c_5069])).

cnf(c_14811,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14758])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_4644,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11236,plain,
    ( k2_funct_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11230,c_4644])).

cnf(c_11264,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11236])).

cnf(c_13956,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | k2_funct_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11236,c_57,c_55,c_5028,c_5062,c_11264])).

cnf(c_13957,plain,
    ( k2_funct_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_13956])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_412,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_413,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_412])).

cnf(c_499,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_413])).

cnf(c_13682,plain,
    ( ~ r2_hidden(sK0(X0,k1_relat_1(sK3)),X0)
    | ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_13688,plain,
    ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13682])).

cnf(c_13690,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_relat_1(sK3)),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13688])).

cnf(c_36,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_692,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_36,c_9])).

cnf(c_696,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_692,c_34])).

cnf(c_697,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_696])).

cnf(c_4611,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_5655,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4617,c_4611])).

cnf(c_41,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_4626,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_10420,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(k6_partfun1(X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4626,c_4627])).

cnf(c_18,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f142])).

cnf(c_10456,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10420,c_18])).

cnf(c_48,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_funct_2(X0,k1_xboole_0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_tarski(X1,X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_4621,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_10689,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X0) != iProver_top
    | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10456,c_4621])).

cnf(c_39,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_42,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_671,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | X3 != X1
    | k6_partfun1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_39,c_42])).

cnf(c_672,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X1)
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(k6_partfun1(X0)) ),
    inference(unflattening,[status(thm)],[c_671])).

cnf(c_24,plain,
    ( v1_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_676,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_2(k6_partfun1(X0),X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_672,c_24])).

cnf(c_677,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X1)
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(renaming,[status(thm)],[c_676])).

cnf(c_4612,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X1) = iProver_top
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_10693,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10456,c_4612])).

cnf(c_10732,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top
    | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10689,c_10693])).

cnf(c_21,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f145])).

cnf(c_10733,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10732,c_21])).

cnf(c_4637,plain,
    ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5513,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_4637])).

cnf(c_11741,plain,
    ( r1_tarski(k1_xboole_0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10733,c_5513])).

cnf(c_11742,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_11741])).

cnf(c_11751,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5655,c_11742])).

cnf(c_11267,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11260])).

cnf(c_44,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_4624,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_11234,plain,
    ( v1_funct_2(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11230,c_4624])).

cnf(c_11253,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11234,c_9667])).

cnf(c_11266,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11253])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_4642,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11235,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11230,c_4642])).

cnf(c_11246,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11235,c_9667])).

cnf(c_3620,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_7338,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | k2_funct_1(sK3) != X0
    | sK1 != X2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_3620])).

cnf(c_7836,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | k2_funct_1(sK3) != X0
    | sK1 != sK1
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_7338])).

cnf(c_7837,plain,
    ( k2_funct_1(sK3) != X0
    | sK1 != sK1
    | sK2 != X1
    | v1_funct_2(X0,X1,sK1) != iProver_top
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7836])).

cnf(c_7839,plain,
    ( k2_funct_1(sK3) != k1_xboole_0
    | sK1 != sK1
    | sK2 != k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7837])).

cnf(c_3601,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6764,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3601])).

cnf(c_3602,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5510,plain,
    ( k1_relat_1(sK3) != X0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_3602])).

cnf(c_6763,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5510])).

cnf(c_35,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_713,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_35,c_11])).

cnf(c_717,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_713,c_34])).

cnf(c_718,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_717])).

cnf(c_4610,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_5641,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4626,c_4610])).

cnf(c_5643,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5641,c_18])).

cnf(c_5649,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5643])).

cnf(c_5495,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_3601])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_5436,plain,
    ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0)
    | r1_tarski(X0,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5442,plain,
    ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5436])).

cnf(c_5444,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_relat_1(sK3)),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5442])).

cnf(c_5128,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_697])).

cnf(c_5129,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5128])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_180,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18045,c_14811,c_14758,c_13957,c_13690,c_11751,c_11267,c_11266,c_11246,c_7839,c_6764,c_6763,c_5649,c_5495,c_5444,c_5129,c_5128,c_5063,c_5062,c_5029,c_5028,c_5020,c_180,c_60,c_55,c_58,c_57])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.96/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.01  
% 3.96/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.96/1.01  
% 3.96/1.01  ------  iProver source info
% 3.96/1.01  
% 3.96/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.96/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.96/1.01  git: non_committed_changes: false
% 3.96/1.01  git: last_make_outside_of_git: false
% 3.96/1.01  
% 3.96/1.01  ------ 
% 3.96/1.01  
% 3.96/1.01  ------ Input Options
% 3.96/1.01  
% 3.96/1.01  --out_options                           all
% 3.96/1.01  --tptp_safe_out                         true
% 3.96/1.01  --problem_path                          ""
% 3.96/1.01  --include_path                          ""
% 3.96/1.01  --clausifier                            res/vclausify_rel
% 3.96/1.01  --clausifier_options                    --mode clausify
% 3.96/1.01  --stdin                                 false
% 3.96/1.01  --stats_out                             all
% 3.96/1.01  
% 3.96/1.01  ------ General Options
% 3.96/1.01  
% 3.96/1.01  --fof                                   false
% 3.96/1.01  --time_out_real                         305.
% 3.96/1.01  --time_out_virtual                      -1.
% 3.96/1.01  --symbol_type_check                     false
% 3.96/1.01  --clausify_out                          false
% 3.96/1.01  --sig_cnt_out                           false
% 3.96/1.01  --trig_cnt_out                          false
% 3.96/1.01  --trig_cnt_out_tolerance                1.
% 3.96/1.01  --trig_cnt_out_sk_spl                   false
% 3.96/1.01  --abstr_cl_out                          false
% 3.96/1.01  
% 3.96/1.01  ------ Global Options
% 3.96/1.01  
% 3.96/1.01  --schedule                              default
% 3.96/1.01  --add_important_lit                     false
% 3.96/1.01  --prop_solver_per_cl                    1000
% 3.96/1.01  --min_unsat_core                        false
% 3.96/1.01  --soft_assumptions                      false
% 3.96/1.01  --soft_lemma_size                       3
% 3.96/1.01  --prop_impl_unit_size                   0
% 3.96/1.01  --prop_impl_unit                        []
% 3.96/1.01  --share_sel_clauses                     true
% 3.96/1.01  --reset_solvers                         false
% 3.96/1.01  --bc_imp_inh                            [conj_cone]
% 3.96/1.01  --conj_cone_tolerance                   3.
% 3.96/1.01  --extra_neg_conj                        none
% 3.96/1.01  --large_theory_mode                     true
% 3.96/1.01  --prolific_symb_bound                   200
% 3.96/1.01  --lt_threshold                          2000
% 3.96/1.01  --clause_weak_htbl                      true
% 3.96/1.01  --gc_record_bc_elim                     false
% 3.96/1.01  
% 3.96/1.01  ------ Preprocessing Options
% 3.96/1.01  
% 3.96/1.01  --preprocessing_flag                    true
% 3.96/1.01  --time_out_prep_mult                    0.1
% 3.96/1.01  --splitting_mode                        input
% 3.96/1.01  --splitting_grd                         true
% 3.96/1.01  --splitting_cvd                         false
% 3.96/1.01  --splitting_cvd_svl                     false
% 3.96/1.01  --splitting_nvd                         32
% 3.96/1.01  --sub_typing                            true
% 3.96/1.01  --prep_gs_sim                           true
% 3.96/1.01  --prep_unflatten                        true
% 3.96/1.01  --prep_res_sim                          true
% 3.96/1.01  --prep_upred                            true
% 3.96/1.01  --prep_sem_filter                       exhaustive
% 3.96/1.01  --prep_sem_filter_out                   false
% 3.96/1.01  --pred_elim                             true
% 3.96/1.01  --res_sim_input                         true
% 3.96/1.01  --eq_ax_congr_red                       true
% 3.96/1.01  --pure_diseq_elim                       true
% 3.96/1.01  --brand_transform                       false
% 3.96/1.01  --non_eq_to_eq                          false
% 3.96/1.01  --prep_def_merge                        true
% 3.96/1.01  --prep_def_merge_prop_impl              false
% 3.96/1.01  --prep_def_merge_mbd                    true
% 3.96/1.01  --prep_def_merge_tr_red                 false
% 3.96/1.01  --prep_def_merge_tr_cl                  false
% 3.96/1.01  --smt_preprocessing                     true
% 3.96/1.01  --smt_ac_axioms                         fast
% 3.96/1.01  --preprocessed_out                      false
% 3.96/1.01  --preprocessed_stats                    false
% 3.96/1.01  
% 3.96/1.01  ------ Abstraction refinement Options
% 3.96/1.01  
% 3.96/1.01  --abstr_ref                             []
% 3.96/1.01  --abstr_ref_prep                        false
% 3.96/1.01  --abstr_ref_until_sat                   false
% 3.96/1.01  --abstr_ref_sig_restrict                funpre
% 3.96/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.96/1.01  --abstr_ref_under                       []
% 3.96/1.01  
% 3.96/1.01  ------ SAT Options
% 3.96/1.01  
% 3.96/1.01  --sat_mode                              false
% 3.96/1.01  --sat_fm_restart_options                ""
% 3.96/1.01  --sat_gr_def                            false
% 3.96/1.01  --sat_epr_types                         true
% 3.96/1.01  --sat_non_cyclic_types                  false
% 3.96/1.01  --sat_finite_models                     false
% 3.96/1.01  --sat_fm_lemmas                         false
% 3.96/1.01  --sat_fm_prep                           false
% 3.96/1.01  --sat_fm_uc_incr                        true
% 3.96/1.01  --sat_out_model                         small
% 3.96/1.01  --sat_out_clauses                       false
% 3.96/1.01  
% 3.96/1.01  ------ QBF Options
% 3.96/1.01  
% 3.96/1.01  --qbf_mode                              false
% 3.96/1.01  --qbf_elim_univ                         false
% 3.96/1.01  --qbf_dom_inst                          none
% 3.96/1.01  --qbf_dom_pre_inst                      false
% 3.96/1.01  --qbf_sk_in                             false
% 3.96/1.01  --qbf_pred_elim                         true
% 3.96/1.01  --qbf_split                             512
% 3.96/1.01  
% 3.96/1.01  ------ BMC1 Options
% 3.96/1.01  
% 3.96/1.01  --bmc1_incremental                      false
% 3.96/1.01  --bmc1_axioms                           reachable_all
% 3.96/1.01  --bmc1_min_bound                        0
% 3.96/1.01  --bmc1_max_bound                        -1
% 3.96/1.01  --bmc1_max_bound_default                -1
% 3.96/1.01  --bmc1_symbol_reachability              true
% 3.96/1.01  --bmc1_property_lemmas                  false
% 3.96/1.01  --bmc1_k_induction                      false
% 3.96/1.01  --bmc1_non_equiv_states                 false
% 3.96/1.01  --bmc1_deadlock                         false
% 3.96/1.01  --bmc1_ucm                              false
% 3.96/1.01  --bmc1_add_unsat_core                   none
% 3.96/1.01  --bmc1_unsat_core_children              false
% 3.96/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.96/1.01  --bmc1_out_stat                         full
% 3.96/1.01  --bmc1_ground_init                      false
% 3.96/1.01  --bmc1_pre_inst_next_state              false
% 3.96/1.01  --bmc1_pre_inst_state                   false
% 3.96/1.01  --bmc1_pre_inst_reach_state             false
% 3.96/1.01  --bmc1_out_unsat_core                   false
% 3.96/1.01  --bmc1_aig_witness_out                  false
% 3.96/1.01  --bmc1_verbose                          false
% 3.96/1.01  --bmc1_dump_clauses_tptp                false
% 3.96/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.96/1.01  --bmc1_dump_file                        -
% 3.96/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.96/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.96/1.01  --bmc1_ucm_extend_mode                  1
% 3.96/1.01  --bmc1_ucm_init_mode                    2
% 3.96/1.01  --bmc1_ucm_cone_mode                    none
% 3.96/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.96/1.01  --bmc1_ucm_relax_model                  4
% 3.96/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.96/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.96/1.01  --bmc1_ucm_layered_model                none
% 3.96/1.01  --bmc1_ucm_max_lemma_size               10
% 3.96/1.01  
% 3.96/1.01  ------ AIG Options
% 3.96/1.01  
% 3.96/1.01  --aig_mode                              false
% 3.96/1.01  
% 3.96/1.01  ------ Instantiation Options
% 3.96/1.01  
% 3.96/1.01  --instantiation_flag                    true
% 3.96/1.01  --inst_sos_flag                         false
% 3.96/1.01  --inst_sos_phase                        true
% 3.96/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.96/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.96/1.01  --inst_lit_sel_side                     num_symb
% 3.96/1.01  --inst_solver_per_active                1400
% 3.96/1.01  --inst_solver_calls_frac                1.
% 3.96/1.01  --inst_passive_queue_type               priority_queues
% 3.96/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.96/1.01  --inst_passive_queues_freq              [25;2]
% 3.96/1.01  --inst_dismatching                      true
% 3.96/1.01  --inst_eager_unprocessed_to_passive     true
% 3.96/1.01  --inst_prop_sim_given                   true
% 3.96/1.01  --inst_prop_sim_new                     false
% 3.96/1.01  --inst_subs_new                         false
% 3.96/1.01  --inst_eq_res_simp                      false
% 3.96/1.01  --inst_subs_given                       false
% 3.96/1.01  --inst_orphan_elimination               true
% 3.96/1.01  --inst_learning_loop_flag               true
% 3.96/1.01  --inst_learning_start                   3000
% 3.96/1.01  --inst_learning_factor                  2
% 3.96/1.01  --inst_start_prop_sim_after_learn       3
% 3.96/1.01  --inst_sel_renew                        solver
% 3.96/1.01  --inst_lit_activity_flag                true
% 3.96/1.01  --inst_restr_to_given                   false
% 3.96/1.01  --inst_activity_threshold               500
% 3.96/1.01  --inst_out_proof                        true
% 3.96/1.01  
% 3.96/1.01  ------ Resolution Options
% 3.96/1.01  
% 3.96/1.01  --resolution_flag                       true
% 3.96/1.01  --res_lit_sel                           adaptive
% 3.96/1.01  --res_lit_sel_side                      none
% 3.96/1.01  --res_ordering                          kbo
% 3.96/1.01  --res_to_prop_solver                    active
% 3.96/1.01  --res_prop_simpl_new                    false
% 3.96/1.01  --res_prop_simpl_given                  true
% 3.96/1.01  --res_passive_queue_type                priority_queues
% 3.96/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.96/1.01  --res_passive_queues_freq               [15;5]
% 3.96/1.01  --res_forward_subs                      full
% 3.96/1.01  --res_backward_subs                     full
% 3.96/1.01  --res_forward_subs_resolution           true
% 3.96/1.01  --res_backward_subs_resolution          true
% 3.96/1.01  --res_orphan_elimination                true
% 3.96/1.01  --res_time_limit                        2.
% 3.96/1.01  --res_out_proof                         true
% 3.96/1.01  
% 3.96/1.01  ------ Superposition Options
% 3.96/1.01  
% 3.96/1.01  --superposition_flag                    true
% 3.96/1.01  --sup_passive_queue_type                priority_queues
% 3.96/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.96/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.96/1.01  --demod_completeness_check              fast
% 3.96/1.01  --demod_use_ground                      true
% 3.96/1.01  --sup_to_prop_solver                    passive
% 3.96/1.01  --sup_prop_simpl_new                    true
% 3.96/1.01  --sup_prop_simpl_given                  true
% 3.96/1.01  --sup_fun_splitting                     false
% 3.96/1.01  --sup_smt_interval                      50000
% 3.96/1.01  
% 3.96/1.01  ------ Superposition Simplification Setup
% 3.96/1.01  
% 3.96/1.01  --sup_indices_passive                   []
% 3.96/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.96/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.01  --sup_full_bw                           [BwDemod]
% 3.96/1.01  --sup_immed_triv                        [TrivRules]
% 3.96/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.01  --sup_immed_bw_main                     []
% 3.96/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.96/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/1.01  
% 3.96/1.01  ------ Combination Options
% 3.96/1.01  
% 3.96/1.01  --comb_res_mult                         3
% 3.96/1.01  --comb_sup_mult                         2
% 3.96/1.01  --comb_inst_mult                        10
% 3.96/1.01  
% 3.96/1.01  ------ Debug Options
% 3.96/1.01  
% 3.96/1.01  --dbg_backtrace                         false
% 3.96/1.01  --dbg_dump_prop_clauses                 false
% 3.96/1.01  --dbg_dump_prop_clauses_file            -
% 3.96/1.01  --dbg_out_stat                          false
% 3.96/1.01  ------ Parsing...
% 3.96/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.96/1.01  
% 3.96/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.96/1.01  
% 3.96/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.96/1.01  
% 3.96/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.01  ------ Proving...
% 3.96/1.01  ------ Problem Properties 
% 3.96/1.01  
% 3.96/1.01  
% 3.96/1.01  clauses                                 49
% 3.96/1.01  conjectures                             6
% 3.96/1.01  EPR                                     6
% 3.96/1.01  Horn                                    46
% 3.96/1.01  unary                                   13
% 3.96/1.01  binary                                  13
% 3.96/1.01  lits                                    131
% 3.96/1.01  lits eq                                 28
% 3.96/1.01  fd_pure                                 0
% 3.96/1.01  fd_pseudo                               0
% 3.96/1.01  fd_cond                                 4
% 3.96/1.01  fd_pseudo_cond                          1
% 3.96/1.01  AC symbols                              0
% 3.96/1.01  
% 3.96/1.01  ------ Schedule dynamic 5 is on 
% 3.96/1.01  
% 3.96/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.96/1.01  
% 3.96/1.01  
% 3.96/1.01  ------ 
% 3.96/1.01  Current options:
% 3.96/1.01  ------ 
% 3.96/1.01  
% 3.96/1.01  ------ Input Options
% 3.96/1.01  
% 3.96/1.01  --out_options                           all
% 3.96/1.01  --tptp_safe_out                         true
% 3.96/1.01  --problem_path                          ""
% 3.96/1.01  --include_path                          ""
% 3.96/1.01  --clausifier                            res/vclausify_rel
% 3.96/1.01  --clausifier_options                    --mode clausify
% 3.96/1.01  --stdin                                 false
% 3.96/1.01  --stats_out                             all
% 3.96/1.01  
% 3.96/1.01  ------ General Options
% 3.96/1.01  
% 3.96/1.01  --fof                                   false
% 3.96/1.01  --time_out_real                         305.
% 3.96/1.01  --time_out_virtual                      -1.
% 3.96/1.01  --symbol_type_check                     false
% 3.96/1.01  --clausify_out                          false
% 3.96/1.01  --sig_cnt_out                           false
% 3.96/1.01  --trig_cnt_out                          false
% 3.96/1.01  --trig_cnt_out_tolerance                1.
% 3.96/1.01  --trig_cnt_out_sk_spl                   false
% 3.96/1.01  --abstr_cl_out                          false
% 3.96/1.01  
% 3.96/1.01  ------ Global Options
% 3.96/1.01  
% 3.96/1.01  --schedule                              default
% 3.96/1.01  --add_important_lit                     false
% 3.96/1.01  --prop_solver_per_cl                    1000
% 3.96/1.01  --min_unsat_core                        false
% 3.96/1.01  --soft_assumptions                      false
% 3.96/1.01  --soft_lemma_size                       3
% 3.96/1.01  --prop_impl_unit_size                   0
% 3.96/1.01  --prop_impl_unit                        []
% 3.96/1.01  --share_sel_clauses                     true
% 3.96/1.01  --reset_solvers                         false
% 3.96/1.01  --bc_imp_inh                            [conj_cone]
% 3.96/1.01  --conj_cone_tolerance                   3.
% 3.96/1.01  --extra_neg_conj                        none
% 3.96/1.01  --large_theory_mode                     true
% 3.96/1.01  --prolific_symb_bound                   200
% 3.96/1.01  --lt_threshold                          2000
% 3.96/1.01  --clause_weak_htbl                      true
% 3.96/1.01  --gc_record_bc_elim                     false
% 3.96/1.01  
% 3.96/1.01  ------ Preprocessing Options
% 3.96/1.01  
% 3.96/1.01  --preprocessing_flag                    true
% 3.96/1.01  --time_out_prep_mult                    0.1
% 3.96/1.01  --splitting_mode                        input
% 3.96/1.01  --splitting_grd                         true
% 3.96/1.01  --splitting_cvd                         false
% 3.96/1.01  --splitting_cvd_svl                     false
% 3.96/1.01  --splitting_nvd                         32
% 3.96/1.01  --sub_typing                            true
% 3.96/1.01  --prep_gs_sim                           true
% 3.96/1.01  --prep_unflatten                        true
% 3.96/1.01  --prep_res_sim                          true
% 3.96/1.01  --prep_upred                            true
% 3.96/1.01  --prep_sem_filter                       exhaustive
% 3.96/1.01  --prep_sem_filter_out                   false
% 3.96/1.01  --pred_elim                             true
% 3.96/1.01  --res_sim_input                         true
% 3.96/1.01  --eq_ax_congr_red                       true
% 3.96/1.01  --pure_diseq_elim                       true
% 3.96/1.01  --brand_transform                       false
% 3.96/1.01  --non_eq_to_eq                          false
% 3.96/1.01  --prep_def_merge                        true
% 3.96/1.01  --prep_def_merge_prop_impl              false
% 3.96/1.01  --prep_def_merge_mbd                    true
% 3.96/1.01  --prep_def_merge_tr_red                 false
% 3.96/1.01  --prep_def_merge_tr_cl                  false
% 3.96/1.01  --smt_preprocessing                     true
% 3.96/1.01  --smt_ac_axioms                         fast
% 3.96/1.01  --preprocessed_out                      false
% 3.96/1.01  --preprocessed_stats                    false
% 3.96/1.01  
% 3.96/1.01  ------ Abstraction refinement Options
% 3.96/1.01  
% 3.96/1.01  --abstr_ref                             []
% 3.96/1.01  --abstr_ref_prep                        false
% 3.96/1.01  --abstr_ref_until_sat                   false
% 3.96/1.01  --abstr_ref_sig_restrict                funpre
% 3.96/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.96/1.01  --abstr_ref_under                       []
% 3.96/1.01  
% 3.96/1.01  ------ SAT Options
% 3.96/1.01  
% 3.96/1.01  --sat_mode                              false
% 3.96/1.01  --sat_fm_restart_options                ""
% 3.96/1.01  --sat_gr_def                            false
% 3.96/1.01  --sat_epr_types                         true
% 3.96/1.01  --sat_non_cyclic_types                  false
% 3.96/1.01  --sat_finite_models                     false
% 3.96/1.01  --sat_fm_lemmas                         false
% 3.96/1.01  --sat_fm_prep                           false
% 3.96/1.01  --sat_fm_uc_incr                        true
% 3.96/1.01  --sat_out_model                         small
% 3.96/1.01  --sat_out_clauses                       false
% 3.96/1.01  
% 3.96/1.01  ------ QBF Options
% 3.96/1.01  
% 3.96/1.01  --qbf_mode                              false
% 3.96/1.01  --qbf_elim_univ                         false
% 3.96/1.01  --qbf_dom_inst                          none
% 3.96/1.01  --qbf_dom_pre_inst                      false
% 3.96/1.01  --qbf_sk_in                             false
% 3.96/1.01  --qbf_pred_elim                         true
% 3.96/1.01  --qbf_split                             512
% 3.96/1.01  
% 3.96/1.01  ------ BMC1 Options
% 3.96/1.01  
% 3.96/1.01  --bmc1_incremental                      false
% 3.96/1.01  --bmc1_axioms                           reachable_all
% 3.96/1.01  --bmc1_min_bound                        0
% 3.96/1.01  --bmc1_max_bound                        -1
% 3.96/1.01  --bmc1_max_bound_default                -1
% 3.96/1.01  --bmc1_symbol_reachability              true
% 3.96/1.01  --bmc1_property_lemmas                  false
% 3.96/1.01  --bmc1_k_induction                      false
% 3.96/1.01  --bmc1_non_equiv_states                 false
% 3.96/1.01  --bmc1_deadlock                         false
% 3.96/1.01  --bmc1_ucm                              false
% 3.96/1.01  --bmc1_add_unsat_core                   none
% 3.96/1.01  --bmc1_unsat_core_children              false
% 3.96/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.96/1.01  --bmc1_out_stat                         full
% 3.96/1.01  --bmc1_ground_init                      false
% 3.96/1.01  --bmc1_pre_inst_next_state              false
% 3.96/1.01  --bmc1_pre_inst_state                   false
% 3.96/1.01  --bmc1_pre_inst_reach_state             false
% 3.96/1.01  --bmc1_out_unsat_core                   false
% 3.96/1.01  --bmc1_aig_witness_out                  false
% 3.96/1.01  --bmc1_verbose                          false
% 3.96/1.01  --bmc1_dump_clauses_tptp                false
% 3.96/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.96/1.01  --bmc1_dump_file                        -
% 3.96/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.96/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.96/1.01  --bmc1_ucm_extend_mode                  1
% 3.96/1.01  --bmc1_ucm_init_mode                    2
% 3.96/1.01  --bmc1_ucm_cone_mode                    none
% 3.96/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.96/1.01  --bmc1_ucm_relax_model                  4
% 3.96/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.96/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.96/1.01  --bmc1_ucm_layered_model                none
% 3.96/1.01  --bmc1_ucm_max_lemma_size               10
% 3.96/1.01  
% 3.96/1.01  ------ AIG Options
% 3.96/1.01  
% 3.96/1.01  --aig_mode                              false
% 3.96/1.01  
% 3.96/1.01  ------ Instantiation Options
% 3.96/1.01  
% 3.96/1.01  --instantiation_flag                    true
% 3.96/1.01  --inst_sos_flag                         false
% 3.96/1.01  --inst_sos_phase                        true
% 3.96/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.96/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.96/1.01  --inst_lit_sel_side                     none
% 3.96/1.01  --inst_solver_per_active                1400
% 3.96/1.01  --inst_solver_calls_frac                1.
% 3.96/1.01  --inst_passive_queue_type               priority_queues
% 3.96/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.96/1.01  --inst_passive_queues_freq              [25;2]
% 3.96/1.01  --inst_dismatching                      true
% 3.96/1.01  --inst_eager_unprocessed_to_passive     true
% 3.96/1.01  --inst_prop_sim_given                   true
% 3.96/1.01  --inst_prop_sim_new                     false
% 3.96/1.01  --inst_subs_new                         false
% 3.96/1.01  --inst_eq_res_simp                      false
% 3.96/1.01  --inst_subs_given                       false
% 3.96/1.01  --inst_orphan_elimination               true
% 3.96/1.01  --inst_learning_loop_flag               true
% 3.96/1.01  --inst_learning_start                   3000
% 3.96/1.01  --inst_learning_factor                  2
% 3.96/1.01  --inst_start_prop_sim_after_learn       3
% 3.96/1.01  --inst_sel_renew                        solver
% 3.96/1.01  --inst_lit_activity_flag                true
% 3.96/1.01  --inst_restr_to_given                   false
% 3.96/1.01  --inst_activity_threshold               500
% 3.96/1.01  --inst_out_proof                        true
% 3.96/1.01  
% 3.96/1.01  ------ Resolution Options
% 3.96/1.01  
% 3.96/1.01  --resolution_flag                       false
% 3.96/1.01  --res_lit_sel                           adaptive
% 3.96/1.01  --res_lit_sel_side                      none
% 3.96/1.01  --res_ordering                          kbo
% 3.96/1.01  --res_to_prop_solver                    active
% 3.96/1.01  --res_prop_simpl_new                    false
% 3.96/1.01  --res_prop_simpl_given                  true
% 3.96/1.01  --res_passive_queue_type                priority_queues
% 3.96/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.96/1.01  --res_passive_queues_freq               [15;5]
% 3.96/1.01  --res_forward_subs                      full
% 3.96/1.01  --res_backward_subs                     full
% 3.96/1.01  --res_forward_subs_resolution           true
% 3.96/1.01  --res_backward_subs_resolution          true
% 3.96/1.01  --res_orphan_elimination                true
% 3.96/1.01  --res_time_limit                        2.
% 3.96/1.01  --res_out_proof                         true
% 3.96/1.01  
% 3.96/1.01  ------ Superposition Options
% 3.96/1.01  
% 3.96/1.01  --superposition_flag                    true
% 3.96/1.01  --sup_passive_queue_type                priority_queues
% 3.96/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.96/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.96/1.01  --demod_completeness_check              fast
% 3.96/1.01  --demod_use_ground                      true
% 3.96/1.01  --sup_to_prop_solver                    passive
% 3.96/1.01  --sup_prop_simpl_new                    true
% 3.96/1.01  --sup_prop_simpl_given                  true
% 3.96/1.01  --sup_fun_splitting                     false
% 3.96/1.01  --sup_smt_interval                      50000
% 3.96/1.01  
% 3.96/1.01  ------ Superposition Simplification Setup
% 3.96/1.01  
% 3.96/1.01  --sup_indices_passive                   []
% 3.96/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.96/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.01  --sup_full_bw                           [BwDemod]
% 3.96/1.01  --sup_immed_triv                        [TrivRules]
% 3.96/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.01  --sup_immed_bw_main                     []
% 3.96/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.96/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/1.01  
% 3.96/1.01  ------ Combination Options
% 3.96/1.01  
% 3.96/1.01  --comb_res_mult                         3
% 3.96/1.01  --comb_sup_mult                         2
% 3.96/1.01  --comb_inst_mult                        10
% 3.96/1.01  
% 3.96/1.01  ------ Debug Options
% 3.96/1.01  
% 3.96/1.01  --dbg_backtrace                         false
% 3.96/1.01  --dbg_dump_prop_clauses                 false
% 3.96/1.01  --dbg_dump_prop_clauses_file            -
% 3.96/1.01  --dbg_out_stat                          false
% 3.96/1.01  
% 3.96/1.01  
% 3.96/1.01  
% 3.96/1.01  
% 3.96/1.01  ------ Proving...
% 3.96/1.01  
% 3.96/1.01  
% 3.96/1.01  % SZS status Theorem for theBenchmark.p
% 3.96/1.01  
% 3.96/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.96/1.01  
% 3.96/1.01  fof(f32,axiom,(
% 3.96/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f69,plain,(
% 3.96/1.01    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.96/1.01    inference(ennf_transformation,[],[f32])).
% 3.96/1.01  
% 3.96/1.01  fof(f70,plain,(
% 3.96/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.96/1.01    inference(flattening,[],[f69])).
% 3.96/1.01  
% 3.96/1.01  fof(f132,plain,(
% 3.96/1.01    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f70])).
% 3.96/1.01  
% 3.96/1.01  fof(f33,conjecture,(
% 3.96/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f34,negated_conjecture,(
% 3.96/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.96/1.01    inference(negated_conjecture,[],[f33])).
% 3.96/1.01  
% 3.96/1.01  fof(f71,plain,(
% 3.96/1.01    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.96/1.01    inference(ennf_transformation,[],[f34])).
% 3.96/1.01  
% 3.96/1.01  fof(f72,plain,(
% 3.96/1.01    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.96/1.01    inference(flattening,[],[f71])).
% 3.96/1.01  
% 3.96/1.01  fof(f81,plain,(
% 3.96/1.01    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.96/1.01    introduced(choice_axiom,[])).
% 3.96/1.01  
% 3.96/1.01  fof(f82,plain,(
% 3.96/1.01    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.96/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f72,f81])).
% 3.96/1.01  
% 3.96/1.01  fof(f139,plain,(
% 3.96/1.01    v2_funct_1(sK3)),
% 3.96/1.01    inference(cnf_transformation,[],[f82])).
% 3.96/1.01  
% 3.96/1.01  fof(f20,axiom,(
% 3.96/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f54,plain,(
% 3.96/1.01    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.96/1.01    inference(ennf_transformation,[],[f20])).
% 3.96/1.01  
% 3.96/1.01  fof(f55,plain,(
% 3.96/1.01    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.96/1.01    inference(flattening,[],[f54])).
% 3.96/1.01  
% 3.96/1.01  fof(f113,plain,(
% 3.96/1.01    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f55])).
% 3.96/1.01  
% 3.96/1.01  fof(f136,plain,(
% 3.96/1.01    v1_funct_1(sK3)),
% 3.96/1.01    inference(cnf_transformation,[],[f82])).
% 3.96/1.01  
% 3.96/1.01  fof(f138,plain,(
% 3.96/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.96/1.01    inference(cnf_transformation,[],[f82])).
% 3.96/1.01  
% 3.96/1.01  fof(f24,axiom,(
% 3.96/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f60,plain,(
% 3.96/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.96/1.01    inference(ennf_transformation,[],[f24])).
% 3.96/1.01  
% 3.96/1.01  fof(f117,plain,(
% 3.96/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.96/1.01    inference(cnf_transformation,[],[f60])).
% 3.96/1.01  
% 3.96/1.01  fof(f31,axiom,(
% 3.96/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f67,plain,(
% 3.96/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.96/1.01    inference(ennf_transformation,[],[f31])).
% 3.96/1.01  
% 3.96/1.01  fof(f68,plain,(
% 3.96/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.96/1.01    inference(flattening,[],[f67])).
% 3.96/1.01  
% 3.96/1.01  fof(f129,plain,(
% 3.96/1.01    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f68])).
% 3.96/1.01  
% 3.96/1.01  fof(f112,plain,(
% 3.96/1.01    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f55])).
% 3.96/1.01  
% 3.96/1.01  fof(f26,axiom,(
% 3.96/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f62,plain,(
% 3.96/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.96/1.01    inference(ennf_transformation,[],[f26])).
% 3.96/1.01  
% 3.96/1.01  fof(f120,plain,(
% 3.96/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.96/1.01    inference(cnf_transformation,[],[f62])).
% 3.96/1.01  
% 3.96/1.01  fof(f140,plain,(
% 3.96/1.01    k2_relset_1(sK1,sK2,sK3) = sK2),
% 3.96/1.01    inference(cnf_transformation,[],[f82])).
% 3.96/1.01  
% 3.96/1.01  fof(f15,axiom,(
% 3.96/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f46,plain,(
% 3.96/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.96/1.01    inference(ennf_transformation,[],[f15])).
% 3.96/1.01  
% 3.96/1.01  fof(f47,plain,(
% 3.96/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.96/1.01    inference(flattening,[],[f46])).
% 3.96/1.01  
% 3.96/1.01  fof(f106,plain,(
% 3.96/1.01    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f47])).
% 3.96/1.01  
% 3.96/1.01  fof(f105,plain,(
% 3.96/1.01    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f47])).
% 3.96/1.01  
% 3.96/1.01  fof(f27,axiom,(
% 3.96/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f63,plain,(
% 3.96/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.96/1.01    inference(ennf_transformation,[],[f27])).
% 3.96/1.01  
% 3.96/1.01  fof(f64,plain,(
% 3.96/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.96/1.01    inference(flattening,[],[f63])).
% 3.96/1.01  
% 3.96/1.01  fof(f121,plain,(
% 3.96/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 3.96/1.01    inference(cnf_transformation,[],[f64])).
% 3.96/1.01  
% 3.96/1.01  fof(f141,plain,(
% 3.96/1.01    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 3.96/1.01    inference(cnf_transformation,[],[f82])).
% 3.96/1.01  
% 3.96/1.01  fof(f10,axiom,(
% 3.96/1.01    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f42,plain,(
% 3.96/1.01    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.96/1.01    inference(ennf_transformation,[],[f10])).
% 3.96/1.01  
% 3.96/1.01  fof(f43,plain,(
% 3.96/1.01    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.96/1.01    inference(flattening,[],[f42])).
% 3.96/1.01  
% 3.96/1.01  fof(f98,plain,(
% 3.96/1.01    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f43])).
% 3.96/1.01  
% 3.96/1.01  fof(f5,axiom,(
% 3.96/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f37,plain,(
% 3.96/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.96/1.01    inference(ennf_transformation,[],[f5])).
% 3.96/1.01  
% 3.96/1.01  fof(f90,plain,(
% 3.96/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f37])).
% 3.96/1.01  
% 3.96/1.01  fof(f4,axiom,(
% 3.96/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f77,plain,(
% 3.96/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.96/1.01    inference(nnf_transformation,[],[f4])).
% 3.96/1.01  
% 3.96/1.01  fof(f89,plain,(
% 3.96/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f77])).
% 3.96/1.01  
% 3.96/1.01  fof(f25,axiom,(
% 3.96/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f61,plain,(
% 3.96/1.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.96/1.01    inference(ennf_transformation,[],[f25])).
% 3.96/1.01  
% 3.96/1.01  fof(f118,plain,(
% 3.96/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.96/1.01    inference(cnf_transformation,[],[f61])).
% 3.96/1.01  
% 3.96/1.01  fof(f6,axiom,(
% 3.96/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f38,plain,(
% 3.96/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.96/1.01    inference(ennf_transformation,[],[f6])).
% 3.96/1.01  
% 3.96/1.01  fof(f78,plain,(
% 3.96/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.96/1.01    inference(nnf_transformation,[],[f38])).
% 3.96/1.01  
% 3.96/1.01  fof(f91,plain,(
% 3.96/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f78])).
% 3.96/1.01  
% 3.96/1.01  fof(f29,axiom,(
% 3.96/1.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f125,plain,(
% 3.96/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.96/1.01    inference(cnf_transformation,[],[f29])).
% 3.96/1.01  
% 3.96/1.01  fof(f12,axiom,(
% 3.96/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f102,plain,(
% 3.96/1.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.96/1.01    inference(cnf_transformation,[],[f12])).
% 3.96/1.01  
% 3.96/1.01  fof(f30,axiom,(
% 3.96/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f126,plain,(
% 3.96/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f30])).
% 3.96/1.01  
% 3.96/1.01  fof(f142,plain,(
% 3.96/1.01    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.96/1.01    inference(definition_unfolding,[],[f102,f126])).
% 3.96/1.01  
% 3.96/1.01  fof(f133,plain,(
% 3.96/1.01    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 != X0 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f70])).
% 3.96/1.01  
% 3.96/1.01  fof(f152,plain,(
% 3.96/1.01    ( ! [X2,X3,X1] : (v1_funct_2(X3,k1_xboole_0,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3)) )),
% 3.96/1.01    inference(equality_resolution,[],[f133])).
% 3.96/1.01  
% 3.96/1.01  fof(f28,axiom,(
% 3.96/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f65,plain,(
% 3.96/1.01    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.96/1.01    inference(ennf_transformation,[],[f28])).
% 3.96/1.01  
% 3.96/1.01  fof(f66,plain,(
% 3.96/1.01    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.96/1.01    inference(flattening,[],[f65])).
% 3.96/1.01  
% 3.96/1.01  fof(f123,plain,(
% 3.96/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.96/1.01    inference(cnf_transformation,[],[f66])).
% 3.96/1.01  
% 3.96/1.01  fof(f124,plain,(
% 3.96/1.01    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f29])).
% 3.96/1.01  
% 3.96/1.01  fof(f16,axiom,(
% 3.96/1.01    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f108,plain,(
% 3.96/1.01    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 3.96/1.01    inference(cnf_transformation,[],[f16])).
% 3.96/1.01  
% 3.96/1.01  fof(f146,plain,(
% 3.96/1.01    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 3.96/1.01    inference(definition_unfolding,[],[f108,f126])).
% 3.96/1.01  
% 3.96/1.01  fof(f14,axiom,(
% 3.96/1.01    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f104,plain,(
% 3.96/1.01    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.96/1.01    inference(cnf_transformation,[],[f14])).
% 3.96/1.01  
% 3.96/1.01  fof(f145,plain,(
% 3.96/1.01    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.96/1.01    inference(definition_unfolding,[],[f104,f126])).
% 3.96/1.01  
% 3.96/1.01  fof(f128,plain,(
% 3.96/1.01    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f68])).
% 3.96/1.01  
% 3.96/1.01  fof(f11,axiom,(
% 3.96/1.01    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f44,plain,(
% 3.96/1.01    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.96/1.01    inference(ennf_transformation,[],[f11])).
% 3.96/1.01  
% 3.96/1.01  fof(f80,plain,(
% 3.96/1.01    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.96/1.01    inference(nnf_transformation,[],[f44])).
% 3.96/1.01  
% 3.96/1.01  fof(f100,plain,(
% 3.96/1.01    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f80])).
% 3.96/1.01  
% 3.96/1.01  fof(f119,plain,(
% 3.96/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.96/1.01    inference(cnf_transformation,[],[f61])).
% 3.96/1.01  
% 3.96/1.01  fof(f7,axiom,(
% 3.96/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f39,plain,(
% 3.96/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.96/1.01    inference(ennf_transformation,[],[f7])).
% 3.96/1.01  
% 3.96/1.01  fof(f79,plain,(
% 3.96/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.96/1.01    inference(nnf_transformation,[],[f39])).
% 3.96/1.01  
% 3.96/1.01  fof(f93,plain,(
% 3.96/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f79])).
% 3.96/1.01  
% 3.96/1.01  fof(f1,axiom,(
% 3.96/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f35,plain,(
% 3.96/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.96/1.01    inference(ennf_transformation,[],[f1])).
% 3.96/1.01  
% 3.96/1.01  fof(f73,plain,(
% 3.96/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.96/1.01    inference(nnf_transformation,[],[f35])).
% 3.96/1.01  
% 3.96/1.01  fof(f74,plain,(
% 3.96/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.96/1.01    inference(rectify,[],[f73])).
% 3.96/1.01  
% 3.96/1.01  fof(f75,plain,(
% 3.96/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.96/1.01    introduced(choice_axiom,[])).
% 3.96/1.01  
% 3.96/1.01  fof(f76,plain,(
% 3.96/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.96/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f74,f75])).
% 3.96/1.01  
% 3.96/1.01  fof(f84,plain,(
% 3.96/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.96/1.01    inference(cnf_transformation,[],[f76])).
% 3.96/1.01  
% 3.96/1.01  fof(f2,axiom,(
% 3.96/1.01    v1_xboole_0(k1_xboole_0)),
% 3.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/1.01  
% 3.96/1.01  fof(f86,plain,(
% 3.96/1.01    v1_xboole_0(k1_xboole_0)),
% 3.96/1.01    inference(cnf_transformation,[],[f2])).
% 3.96/1.01  
% 3.96/1.01  cnf(c_49,plain,
% 3.96/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.96/1.01      | v1_funct_2(X0,X1,X3)
% 3.96/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.96/1.01      | ~ r1_tarski(X2,X3)
% 3.96/1.01      | ~ v1_funct_1(X0)
% 3.96/1.01      | k1_xboole_0 = X2 ),
% 3.96/1.01      inference(cnf_transformation,[],[f132]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_8290,plain,
% 3.96/1.01      ( v1_funct_2(X0,X1,X2)
% 3.96/1.01      | ~ v1_funct_2(X0,X1,k1_relat_1(sK3))
% 3.96/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_relat_1(sK3))))
% 3.96/1.01      | ~ r1_tarski(k1_relat_1(sK3),X2)
% 3.96/1.01      | ~ v1_funct_1(X0)
% 3.96/1.01      | k1_xboole_0 = k1_relat_1(sK3) ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_49]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_18045,plain,
% 3.96/1.01      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
% 3.96/1.01      | v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.96/1.01      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
% 3.96/1.01      | ~ r1_tarski(k1_relat_1(sK3),sK1)
% 3.96/1.01      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.96/1.01      | k1_xboole_0 = k1_relat_1(sK3) ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_8290]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_54,negated_conjecture,
% 3.96/1.01      ( v2_funct_1(sK3) ),
% 3.96/1.01      inference(cnf_transformation,[],[f139]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_4618,plain,
% 3.96/1.01      ( v2_funct_1(sK3) = iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_29,plain,
% 3.96/1.01      ( ~ v2_funct_1(X0)
% 3.96/1.01      | ~ v1_funct_1(X0)
% 3.96/1.01      | ~ v1_relat_1(X0)
% 3.96/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.96/1.01      inference(cnf_transformation,[],[f113]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_4632,plain,
% 3.96/1.01      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.96/1.01      | v2_funct_1(X0) != iProver_top
% 3.96/1.01      | v1_funct_1(X0) != iProver_top
% 3.96/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_10413,plain,
% 3.96/1.01      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.96/1.01      | v1_funct_1(sK3) != iProver_top
% 3.96/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_4618,c_4632]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_57,negated_conjecture,
% 3.96/1.01      ( v1_funct_1(sK3) ),
% 3.96/1.01      inference(cnf_transformation,[],[f136]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_55,negated_conjecture,
% 3.96/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.96/1.01      inference(cnf_transformation,[],[f138]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_858,plain,
% 3.96/1.01      ( ~ v1_funct_1(X0)
% 3.96/1.01      | ~ v1_relat_1(X0)
% 3.96/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.96/1.01      | sK3 != X0 ),
% 3.96/1.01      inference(resolution_lifted,[status(thm)],[c_29,c_54]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_859,plain,
% 3.96/1.01      ( ~ v1_funct_1(sK3)
% 3.96/1.01      | ~ v1_relat_1(sK3)
% 3.96/1.01      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.96/1.01      inference(unflattening,[status(thm)],[c_858]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_34,plain,
% 3.96/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.96/1.01      | v1_relat_1(X0) ),
% 3.96/1.01      inference(cnf_transformation,[],[f117]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5062,plain,
% 3.96/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.96/1.01      | v1_relat_1(sK3) ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_34]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_11230,plain,
% 3.96/1.01      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.96/1.01      inference(global_propositional_subsumption,
% 3.96/1.01                [status(thm)],
% 3.96/1.01                [c_10413,c_57,c_55,c_859,c_5062]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_43,plain,
% 3.96/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.96/1.01      | ~ v1_funct_1(X0)
% 3.96/1.01      | ~ v1_relat_1(X0) ),
% 3.96/1.01      inference(cnf_transformation,[],[f129]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_4625,plain,
% 3.96/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.96/1.01      | v1_funct_1(X0) != iProver_top
% 3.96/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_11233,plain,
% 3.96/1.01      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 3.96/1.01      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.96/1.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_11230,c_4625]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_30,plain,
% 3.96/1.01      ( ~ v2_funct_1(X0)
% 3.96/1.01      | ~ v1_funct_1(X0)
% 3.96/1.01      | ~ v1_relat_1(X0)
% 3.96/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.96/1.01      inference(cnf_transformation,[],[f112]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_4631,plain,
% 3.96/1.01      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.96/1.01      | v2_funct_1(X0) != iProver_top
% 3.96/1.01      | v1_funct_1(X0) != iProver_top
% 3.96/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_9593,plain,
% 3.96/1.01      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 3.96/1.01      | v1_funct_1(sK3) != iProver_top
% 3.96/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_4618,c_4631]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_4617,plain,
% 3.96/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_37,plain,
% 3.96/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.96/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.96/1.01      inference(cnf_transformation,[],[f120]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_4628,plain,
% 3.96/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.96/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_7932,plain,
% 3.96/1.01      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_4617,c_4628]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_53,negated_conjecture,
% 3.96/1.01      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 3.96/1.01      inference(cnf_transformation,[],[f140]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_7938,plain,
% 3.96/1.01      ( k2_relat_1(sK3) = sK2 ),
% 3.96/1.01      inference(light_normalisation,[status(thm)],[c_7932,c_53]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_9594,plain,
% 3.96/1.01      ( k1_relat_1(k2_funct_1(sK3)) = sK2
% 3.96/1.01      | v1_funct_1(sK3) != iProver_top
% 3.96/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.96/1.01      inference(light_normalisation,[status(thm)],[c_9593,c_7938]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_58,plain,
% 3.96/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_60,plain,
% 3.96/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5063,plain,
% 3.96/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.96/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_5062]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_9667,plain,
% 3.96/1.01      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 3.96/1.01      inference(global_propositional_subsumption,
% 3.96/1.01                [status(thm)],
% 3.96/1.01                [c_9594,c_58,c_60,c_5063]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_11260,plain,
% 3.96/1.01      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 3.96/1.01      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.96/1.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.96/1.01      inference(light_normalisation,[status(thm)],[c_11233,c_9667]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_22,plain,
% 3.96/1.01      ( ~ v1_funct_1(X0)
% 3.96/1.01      | v1_funct_1(k2_funct_1(X0))
% 3.96/1.01      | ~ v1_relat_1(X0) ),
% 3.96/1.01      inference(cnf_transformation,[],[f106]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5020,plain,
% 3.96/1.01      ( v1_funct_1(k2_funct_1(sK3))
% 3.96/1.01      | ~ v1_funct_1(sK3)
% 3.96/1.01      | ~ v1_relat_1(sK3) ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_22]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5021,plain,
% 3.96/1.01      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 3.96/1.01      | v1_funct_1(sK3) != iProver_top
% 3.96/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_5020]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_23,plain,
% 3.96/1.01      ( ~ v1_funct_1(X0)
% 3.96/1.01      | ~ v1_relat_1(X0)
% 3.96/1.01      | v1_relat_1(k2_funct_1(X0)) ),
% 3.96/1.01      inference(cnf_transformation,[],[f105]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5028,plain,
% 3.96/1.01      ( ~ v1_funct_1(sK3)
% 3.96/1.01      | v1_relat_1(k2_funct_1(sK3))
% 3.96/1.01      | ~ v1_relat_1(sK3) ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_23]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5029,plain,
% 3.96/1.01      ( v1_funct_1(sK3) != iProver_top
% 3.96/1.01      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 3.96/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_5028]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_14591,plain,
% 3.96/1.01      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 3.96/1.01      inference(global_propositional_subsumption,
% 3.96/1.01                [status(thm)],
% 3.96/1.01                [c_11260,c_58,c_60,c_5021,c_5029,c_5063]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_38,plain,
% 3.96/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.96/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.96/1.01      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 3.96/1.01      inference(cnf_transformation,[],[f121]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_4627,plain,
% 3.96/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.96/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 3.96/1.01      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_14597,plain,
% 3.96/1.01      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.96/1.01      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),X0) != iProver_top ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_14591,c_4627]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_14635,plain,
% 3.96/1.01      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.96/1.01      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.96/1.01      inference(light_normalisation,[status(thm)],[c_14597,c_11230]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_52,negated_conjecture,
% 3.96/1.01      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.96/1.01      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.96/1.01      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 3.96/1.01      inference(cnf_transformation,[],[f141]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_4619,plain,
% 3.96/1.01      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 3.96/1.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.96/1.01      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_62,plain,
% 3.96/1.01      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 3.96/1.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.96/1.01      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5068,plain,
% 3.96/1.01      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.96/1.01      | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
% 3.96/1.01      inference(global_propositional_subsumption,
% 3.96/1.01                [status(thm)],
% 3.96/1.01                [c_4619,c_58,c_60,c_62,c_5021,c_5063]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5069,plain,
% 3.96/1.01      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 3.96/1.01      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.96/1.01      inference(renaming,[status(thm)],[c_5068]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_14758,plain,
% 3.96/1.01      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 3.96/1.01      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_14635,c_5069]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_14811,plain,
% 3.96/1.01      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.96/1.01      | ~ r1_tarski(k1_relat_1(sK3),sK1) ),
% 3.96/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_14758]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_14,plain,
% 3.96/1.01      ( ~ v1_relat_1(X0)
% 3.96/1.01      | k2_relat_1(X0) != k1_xboole_0
% 3.96/1.01      | k1_xboole_0 = X0 ),
% 3.96/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_4644,plain,
% 3.96/1.01      ( k2_relat_1(X0) != k1_xboole_0
% 3.96/1.01      | k1_xboole_0 = X0
% 3.96/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_11236,plain,
% 3.96/1.01      ( k2_funct_1(sK3) = k1_xboole_0
% 3.96/1.01      | k1_relat_1(sK3) != k1_xboole_0
% 3.96/1.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_11230,c_4644]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_11264,plain,
% 3.96/1.01      ( ~ v1_relat_1(k2_funct_1(sK3))
% 3.96/1.01      | k2_funct_1(sK3) = k1_xboole_0
% 3.96/1.01      | k1_relat_1(sK3) != k1_xboole_0 ),
% 3.96/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_11236]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_13956,plain,
% 3.96/1.01      ( k1_relat_1(sK3) != k1_xboole_0 | k2_funct_1(sK3) = k1_xboole_0 ),
% 3.96/1.01      inference(global_propositional_subsumption,
% 3.96/1.01                [status(thm)],
% 3.96/1.01                [c_11236,c_57,c_55,c_5028,c_5062,c_11264]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_13957,plain,
% 3.96/1.01      ( k2_funct_1(sK3) = k1_xboole_0 | k1_relat_1(sK3) != k1_xboole_0 ),
% 3.96/1.01      inference(renaming,[status(thm)],[c_13956]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_7,plain,
% 3.96/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/1.01      | ~ r2_hidden(X2,X0)
% 3.96/1.01      | ~ v1_xboole_0(X1) ),
% 3.96/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5,plain,
% 3.96/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.96/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_412,plain,
% 3.96/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.96/1.01      inference(prop_impl,[status(thm)],[c_5]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_413,plain,
% 3.96/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.96/1.01      inference(renaming,[status(thm)],[c_412]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_499,plain,
% 3.96/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 3.96/1.01      inference(bin_hyper_res,[status(thm)],[c_7,c_413]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_13682,plain,
% 3.96/1.01      ( ~ r2_hidden(sK0(X0,k1_relat_1(sK3)),X0)
% 3.96/1.01      | ~ r1_tarski(X0,X1)
% 3.96/1.01      | ~ v1_xboole_0(X1) ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_499]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_13688,plain,
% 3.96/1.01      ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0) != iProver_top
% 3.96/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.96/1.01      | v1_xboole_0(X1) != iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_13682]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_13690,plain,
% 3.96/1.01      ( r2_hidden(sK0(k1_xboole_0,k1_relat_1(sK3)),k1_xboole_0) != iProver_top
% 3.96/1.01      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.96/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_13688]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_36,plain,
% 3.96/1.01      ( v4_relat_1(X0,X1)
% 3.96/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.96/1.01      inference(cnf_transformation,[],[f118]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_9,plain,
% 3.96/1.01      ( ~ v4_relat_1(X0,X1)
% 3.96/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 3.96/1.01      | ~ v1_relat_1(X0) ),
% 3.96/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_692,plain,
% 3.96/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.96/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 3.96/1.01      | ~ v1_relat_1(X0) ),
% 3.96/1.01      inference(resolution,[status(thm)],[c_36,c_9]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_696,plain,
% 3.96/1.01      ( r1_tarski(k1_relat_1(X0),X1)
% 3.96/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.96/1.01      inference(global_propositional_subsumption,
% 3.96/1.01                [status(thm)],
% 3.96/1.01                [c_692,c_34]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_697,plain,
% 3.96/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.96/1.01      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.96/1.01      inference(renaming,[status(thm)],[c_696]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_4611,plain,
% 3.96/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.96/1.01      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_697]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5655,plain,
% 3.96/1.01      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_4617,c_4611]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_41,plain,
% 3.96/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.96/1.01      inference(cnf_transformation,[],[f125]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_4626,plain,
% 3.96/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_10420,plain,
% 3.96/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 3.96/1.01      | r1_tarski(k2_relat_1(k6_partfun1(X0)),X1) != iProver_top ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_4626,c_4627]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_18,plain,
% 3.96/1.01      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.96/1.01      inference(cnf_transformation,[],[f142]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_10456,plain,
% 3.96/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 3.96/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.96/1.01      inference(light_normalisation,[status(thm)],[c_10420,c_18]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_48,plain,
% 3.96/1.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.96/1.01      | v1_funct_2(X0,k1_xboole_0,X2)
% 3.96/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.96/1.01      | ~ r1_tarski(X1,X2)
% 3.96/1.01      | ~ v1_funct_1(X0) ),
% 3.96/1.01      inference(cnf_transformation,[],[f152]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_4621,plain,
% 3.96/1.01      ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
% 3.96/1.01      | v1_funct_2(X0,k1_xboole_0,X2) = iProver_top
% 3.96/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 3.96/1.01      | r1_tarski(X1,X2) != iProver_top
% 3.96/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_10689,plain,
% 3.96/1.01      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X0) != iProver_top
% 3.96/1.01      | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X1) = iProver_top
% 3.96/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.96/1.01      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 3.96/1.01      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_10456,c_4621]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_39,plain,
% 3.96/1.01      ( v1_funct_2(X0,X1,X2)
% 3.96/1.01      | ~ v1_partfun1(X0,X1)
% 3.96/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.96/1.01      | ~ v1_funct_1(X0) ),
% 3.96/1.01      inference(cnf_transformation,[],[f123]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_42,plain,
% 3.96/1.01      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 3.96/1.01      inference(cnf_transformation,[],[f124]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_671,plain,
% 3.96/1.01      ( v1_funct_2(X0,X1,X2)
% 3.96/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.96/1.01      | ~ v1_funct_1(X0)
% 3.96/1.01      | X3 != X1
% 3.96/1.01      | k6_partfun1(X3) != X0 ),
% 3.96/1.01      inference(resolution_lifted,[status(thm)],[c_39,c_42]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_672,plain,
% 3.96/1.01      ( v1_funct_2(k6_partfun1(X0),X0,X1)
% 3.96/1.01      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.96/1.01      | ~ v1_funct_1(k6_partfun1(X0)) ),
% 3.96/1.01      inference(unflattening,[status(thm)],[c_671]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_24,plain,
% 3.96/1.01      ( v1_funct_1(k6_partfun1(X0)) ),
% 3.96/1.01      inference(cnf_transformation,[],[f146]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_676,plain,
% 3.96/1.01      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.96/1.01      | v1_funct_2(k6_partfun1(X0),X0,X1) ),
% 3.96/1.01      inference(global_propositional_subsumption,
% 3.96/1.01                [status(thm)],
% 3.96/1.01                [c_672,c_24]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_677,plain,
% 3.96/1.01      ( v1_funct_2(k6_partfun1(X0),X0,X1)
% 3.96/1.01      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.96/1.01      inference(renaming,[status(thm)],[c_676]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_4612,plain,
% 3.96/1.01      ( v1_funct_2(k6_partfun1(X0),X0,X1) = iProver_top
% 3.96/1.01      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_10693,plain,
% 3.96/1.01      ( v1_funct_2(k6_partfun1(X0),X0,X1) = iProver_top
% 3.96/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_10456,c_4612]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_10732,plain,
% 3.96/1.01      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X0) = iProver_top
% 3.96/1.01      | r1_tarski(X1,X0) != iProver_top
% 3.96/1.01      | r1_tarski(k1_xboole_0,X1) != iProver_top
% 3.96/1.01      | v1_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.96/1.01      inference(forward_subsumption_resolution,
% 3.96/1.01                [status(thm)],
% 3.96/1.01                [c_10689,c_10693]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_21,plain,
% 3.96/1.01      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.96/1.01      inference(cnf_transformation,[],[f145]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_10733,plain,
% 3.96/1.01      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 3.96/1.01      | r1_tarski(X1,X0) != iProver_top
% 3.96/1.01      | r1_tarski(k1_xboole_0,X1) != iProver_top
% 3.96/1.01      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.96/1.01      inference(light_normalisation,[status(thm)],[c_10732,c_21]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_4637,plain,
% 3.96/1.01      ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5513,plain,
% 3.96/1.01      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_21,c_4637]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_11741,plain,
% 3.96/1.01      ( r1_tarski(k1_xboole_0,X1) != iProver_top
% 3.96/1.01      | r1_tarski(X1,X0) != iProver_top
% 3.96/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 3.96/1.01      inference(global_propositional_subsumption,
% 3.96/1.01                [status(thm)],
% 3.96/1.01                [c_10733,c_5513]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_11742,plain,
% 3.96/1.01      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 3.96/1.01      | r1_tarski(X1,X0) != iProver_top
% 3.96/1.01      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 3.96/1.01      inference(renaming,[status(thm)],[c_11741]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_11751,plain,
% 3.96/1.01      ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) = iProver_top
% 3.96/1.01      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_5655,c_11742]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_11267,plain,
% 3.96/1.01      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
% 3.96/1.01      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.96/1.01      | ~ v1_relat_1(k2_funct_1(sK3)) ),
% 3.96/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_11260]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_44,plain,
% 3.96/1.01      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.96/1.01      | ~ v1_funct_1(X0)
% 3.96/1.01      | ~ v1_relat_1(X0) ),
% 3.96/1.01      inference(cnf_transformation,[],[f128]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_4624,plain,
% 3.96/1.01      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 3.96/1.01      | v1_funct_1(X0) != iProver_top
% 3.96/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_11234,plain,
% 3.96/1.01      ( v1_funct_2(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)) = iProver_top
% 3.96/1.01      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.96/1.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_11230,c_4624]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_11253,plain,
% 3.96/1.01      ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) = iProver_top
% 3.96/1.01      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.96/1.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.96/1.01      inference(light_normalisation,[status(thm)],[c_11234,c_9667]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_11266,plain,
% 3.96/1.01      ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
% 3.96/1.01      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.96/1.01      | ~ v1_relat_1(k2_funct_1(sK3)) ),
% 3.96/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_11253]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_16,plain,
% 3.96/1.01      ( ~ v1_relat_1(X0)
% 3.96/1.01      | k2_relat_1(X0) != k1_xboole_0
% 3.96/1.01      | k1_relat_1(X0) = k1_xboole_0 ),
% 3.96/1.01      inference(cnf_transformation,[],[f100]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_4642,plain,
% 3.96/1.01      ( k2_relat_1(X0) != k1_xboole_0
% 3.96/1.01      | k1_relat_1(X0) = k1_xboole_0
% 3.96/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_11235,plain,
% 3.96/1.01      ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0
% 3.96/1.01      | k1_relat_1(sK3) != k1_xboole_0
% 3.96/1.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_11230,c_4642]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_11246,plain,
% 3.96/1.01      ( k1_relat_1(sK3) != k1_xboole_0
% 3.96/1.01      | sK2 = k1_xboole_0
% 3.96/1.01      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.96/1.01      inference(demodulation,[status(thm)],[c_11235,c_9667]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_3620,plain,
% 3.96/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.96/1.01      | v1_funct_2(X3,X4,X5)
% 3.96/1.01      | X3 != X0
% 3.96/1.01      | X4 != X1
% 3.96/1.01      | X5 != X2 ),
% 3.96/1.01      theory(equality) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_7338,plain,
% 3.96/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.96/1.01      | v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.96/1.01      | k2_funct_1(sK3) != X0
% 3.96/1.01      | sK1 != X2
% 3.96/1.01      | sK2 != X1 ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_3620]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_7836,plain,
% 3.96/1.01      ( ~ v1_funct_2(X0,X1,sK1)
% 3.96/1.01      | v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.96/1.01      | k2_funct_1(sK3) != X0
% 3.96/1.01      | sK1 != sK1
% 3.96/1.01      | sK2 != X1 ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_7338]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_7837,plain,
% 3.96/1.01      ( k2_funct_1(sK3) != X0
% 3.96/1.01      | sK1 != sK1
% 3.96/1.01      | sK2 != X1
% 3.96/1.01      | v1_funct_2(X0,X1,sK1) != iProver_top
% 3.96/1.01      | v1_funct_2(k2_funct_1(sK3),sK2,sK1) = iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_7836]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_7839,plain,
% 3.96/1.01      ( k2_funct_1(sK3) != k1_xboole_0
% 3.96/1.01      | sK1 != sK1
% 3.96/1.01      | sK2 != k1_xboole_0
% 3.96/1.01      | v1_funct_2(k2_funct_1(sK3),sK2,sK1) = iProver_top
% 3.96/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) != iProver_top ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_7837]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_3601,plain,( X0 = X0 ),theory(equality) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_6764,plain,
% 3.96/1.01      ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_3601]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_3602,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5510,plain,
% 3.96/1.01      ( k1_relat_1(sK3) != X0
% 3.96/1.01      | k1_relat_1(sK3) = k1_xboole_0
% 3.96/1.01      | k1_xboole_0 != X0 ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_3602]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_6763,plain,
% 3.96/1.01      ( k1_relat_1(sK3) != k1_relat_1(sK3)
% 3.96/1.01      | k1_relat_1(sK3) = k1_xboole_0
% 3.96/1.01      | k1_xboole_0 != k1_relat_1(sK3) ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_5510]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_35,plain,
% 3.96/1.01      ( v5_relat_1(X0,X1)
% 3.96/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.96/1.01      inference(cnf_transformation,[],[f119]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_11,plain,
% 3.96/1.01      ( ~ v5_relat_1(X0,X1)
% 3.96/1.01      | r1_tarski(k2_relat_1(X0),X1)
% 3.96/1.01      | ~ v1_relat_1(X0) ),
% 3.96/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_713,plain,
% 3.96/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.96/1.01      | r1_tarski(k2_relat_1(X0),X2)
% 3.96/1.01      | ~ v1_relat_1(X0) ),
% 3.96/1.01      inference(resolution,[status(thm)],[c_35,c_11]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_717,plain,
% 3.96/1.01      ( r1_tarski(k2_relat_1(X0),X2)
% 3.96/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.96/1.01      inference(global_propositional_subsumption,
% 3.96/1.01                [status(thm)],
% 3.96/1.01                [c_713,c_34]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_718,plain,
% 3.96/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.96/1.01      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.96/1.01      inference(renaming,[status(thm)],[c_717]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_4610,plain,
% 3.96/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.96/1.01      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5641,plain,
% 3.96/1.01      ( r1_tarski(k2_relat_1(k6_partfun1(X0)),X0) = iProver_top ),
% 3.96/1.01      inference(superposition,[status(thm)],[c_4626,c_4610]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5643,plain,
% 3.96/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.96/1.01      inference(light_normalisation,[status(thm)],[c_5641,c_18]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5649,plain,
% 3.96/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_5643]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5495,plain,
% 3.96/1.01      ( sK1 = sK1 ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_3601]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_1,plain,
% 3.96/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.96/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5436,plain,
% 3.96/1.01      ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0)
% 3.96/1.01      | r1_tarski(X0,k1_relat_1(sK3)) ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5442,plain,
% 3.96/1.01      ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0) = iProver_top
% 3.96/1.01      | r1_tarski(X0,k1_relat_1(sK3)) = iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_5436]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5444,plain,
% 3.96/1.01      ( r2_hidden(sK0(k1_xboole_0,k1_relat_1(sK3)),k1_xboole_0) = iProver_top
% 3.96/1.01      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) = iProver_top ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_5442]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5128,plain,
% 3.96/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.96/1.01      | r1_tarski(k1_relat_1(sK3),sK1) ),
% 3.96/1.01      inference(instantiation,[status(thm)],[c_697]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_5129,plain,
% 3.96/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.96/1.01      | r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_5128]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_3,plain,
% 3.96/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.96/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(c_180,plain,
% 3.96/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.96/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.96/1.01  
% 3.96/1.01  cnf(contradiction,plain,
% 3.96/1.01      ( $false ),
% 3.96/1.01      inference(minisat,
% 3.96/1.01                [status(thm)],
% 3.96/1.01                [c_18045,c_14811,c_14758,c_13957,c_13690,c_11751,c_11267,
% 3.96/1.01                 c_11266,c_11246,c_7839,c_6764,c_6763,c_5649,c_5495,
% 3.96/1.01                 c_5444,c_5129,c_5128,c_5063,c_5062,c_5029,c_5028,c_5020,
% 3.96/1.01                 c_180,c_60,c_55,c_58,c_57]) ).
% 3.96/1.01  
% 3.96/1.01  
% 3.96/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.96/1.01  
% 3.96/1.01  ------                               Statistics
% 3.96/1.01  
% 3.96/1.01  ------ General
% 3.96/1.01  
% 3.96/1.01  abstr_ref_over_cycles:                  0
% 3.96/1.01  abstr_ref_under_cycles:                 0
% 3.96/1.01  gc_basic_clause_elim:                   0
% 3.96/1.01  forced_gc_time:                         0
% 3.96/1.01  parsing_time:                           0.013
% 3.96/1.01  unif_index_cands_time:                  0.
% 3.96/1.01  unif_index_add_time:                    0.
% 3.96/1.01  orderings_time:                         0.
% 3.96/1.01  out_proof_time:                         0.012
% 3.96/1.01  total_time:                             0.439
% 3.96/1.01  num_of_symbols:                         57
% 3.96/1.01  num_of_terms:                           14724
% 3.96/1.01  
% 3.96/1.01  ------ Preprocessing
% 3.96/1.01  
% 3.96/1.01  num_of_splits:                          0
% 3.96/1.01  num_of_split_atoms:                     0
% 3.96/1.01  num_of_reused_defs:                     0
% 3.96/1.01  num_eq_ax_congr_red:                    20
% 3.96/1.01  num_of_sem_filtered_clauses:            1
% 3.96/1.01  num_of_subtypes:                        0
% 3.96/1.01  monotx_restored_types:                  0
% 3.96/1.01  sat_num_of_epr_types:                   0
% 3.96/1.01  sat_num_of_non_cyclic_types:            0
% 3.96/1.01  sat_guarded_non_collapsed_types:        0
% 3.96/1.01  num_pure_diseq_elim:                    0
% 3.96/1.01  simp_replaced_by:                       0
% 3.96/1.01  res_preprocessed:                       242
% 3.96/1.01  prep_upred:                             0
% 3.96/1.01  prep_unflattend:                        196
% 3.96/1.01  smt_new_axioms:                         0
% 3.96/1.01  pred_elim_cands:                        8
% 3.96/1.01  pred_elim:                              3
% 3.96/1.01  pred_elim_cl:                           5
% 3.96/1.01  pred_elim_cycles:                       7
% 3.96/1.01  merged_defs:                            8
% 3.96/1.01  merged_defs_ncl:                        0
% 3.96/1.01  bin_hyper_res:                          9
% 3.96/1.01  prep_cycles:                            4
% 3.96/1.01  pred_elim_time:                         0.049
% 3.96/1.01  splitting_time:                         0.
% 3.96/1.01  sem_filter_time:                        0.
% 3.96/1.01  monotx_time:                            0.
% 3.96/1.01  subtype_inf_time:                       0.
% 3.96/1.01  
% 3.96/1.01  ------ Problem properties
% 3.96/1.01  
% 3.96/1.01  clauses:                                49
% 3.96/1.01  conjectures:                            6
% 3.96/1.01  epr:                                    6
% 3.96/1.01  horn:                                   46
% 3.96/1.01  ground:                                 8
% 3.96/1.01  unary:                                  13
% 3.96/1.01  binary:                                 13
% 3.96/1.01  lits:                                   131
% 3.96/1.01  lits_eq:                                28
% 3.96/1.01  fd_pure:                                0
% 3.96/1.01  fd_pseudo:                              0
% 3.96/1.01  fd_cond:                                4
% 3.96/1.01  fd_pseudo_cond:                         1
% 3.96/1.01  ac_symbols:                             0
% 3.96/1.01  
% 3.96/1.01  ------ Propositional Solver
% 3.96/1.01  
% 3.96/1.01  prop_solver_calls:                      28
% 3.96/1.01  prop_fast_solver_calls:                 2347
% 3.96/1.01  smt_solver_calls:                       0
% 3.96/1.01  smt_fast_solver_calls:                  0
% 3.96/1.01  prop_num_of_clauses:                    5869
% 3.96/1.01  prop_preprocess_simplified:             15136
% 3.96/1.01  prop_fo_subsumed:                       78
% 3.96/1.01  prop_solver_time:                       0.
% 3.96/1.01  smt_solver_time:                        0.
% 3.96/1.01  smt_fast_solver_time:                   0.
% 3.96/1.01  prop_fast_solver_time:                  0.
% 3.96/1.01  prop_unsat_core_time:                   0.
% 3.96/1.01  
% 3.96/1.01  ------ QBF
% 3.96/1.01  
% 3.96/1.01  qbf_q_res:                              0
% 3.96/1.01  qbf_num_tautologies:                    0
% 3.96/1.01  qbf_prep_cycles:                        0
% 3.96/1.01  
% 3.96/1.01  ------ BMC1
% 3.96/1.01  
% 3.96/1.01  bmc1_current_bound:                     -1
% 3.96/1.01  bmc1_last_solved_bound:                 -1
% 3.96/1.01  bmc1_unsat_core_size:                   -1
% 3.96/1.01  bmc1_unsat_core_parents_size:           -1
% 3.96/1.01  bmc1_merge_next_fun:                    0
% 3.96/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.96/1.01  
% 3.96/1.01  ------ Instantiation
% 3.96/1.01  
% 3.96/1.01  inst_num_of_clauses:                    1608
% 3.96/1.01  inst_num_in_passive:                    351
% 3.96/1.01  inst_num_in_active:                     797
% 3.96/1.01  inst_num_in_unprocessed:                462
% 3.96/1.01  inst_num_of_loops:                      914
% 3.96/1.01  inst_num_of_learning_restarts:          0
% 3.96/1.01  inst_num_moves_active_passive:          114
% 3.96/1.01  inst_lit_activity:                      0
% 3.96/1.01  inst_lit_activity_moves:                0
% 3.96/1.01  inst_num_tautologies:                   0
% 3.96/1.01  inst_num_prop_implied:                  0
% 3.96/1.01  inst_num_existing_simplified:           0
% 3.96/1.01  inst_num_eq_res_simplified:             0
% 3.96/1.01  inst_num_child_elim:                    0
% 3.96/1.01  inst_num_of_dismatching_blockings:      575
% 3.96/1.01  inst_num_of_non_proper_insts:           1412
% 3.96/1.01  inst_num_of_duplicates:                 0
% 3.96/1.01  inst_inst_num_from_inst_to_res:         0
% 3.96/1.01  inst_dismatching_checking_time:         0.
% 3.96/1.01  
% 3.96/1.01  ------ Resolution
% 3.96/1.01  
% 3.96/1.01  res_num_of_clauses:                     0
% 3.96/1.01  res_num_in_passive:                     0
% 3.96/1.01  res_num_in_active:                      0
% 3.96/1.01  res_num_of_loops:                       246
% 3.96/1.01  res_forward_subset_subsumed:            33
% 3.96/1.01  res_backward_subset_subsumed:           8
% 3.96/1.01  res_forward_subsumed:                   0
% 3.96/1.01  res_backward_subsumed:                  0
% 3.96/1.01  res_forward_subsumption_resolution:     0
% 3.96/1.01  res_backward_subsumption_resolution:    0
% 3.96/1.01  res_clause_to_clause_subsumption:       1218
% 3.96/1.01  res_orphan_elimination:                 0
% 3.96/1.01  res_tautology_del:                      85
% 3.96/1.01  res_num_eq_res_simplified:              0
% 3.96/1.01  res_num_sel_changes:                    0
% 3.96/1.01  res_moves_from_active_to_pass:          0
% 3.96/1.01  
% 3.96/1.01  ------ Superposition
% 3.96/1.01  
% 3.96/1.01  sup_time_total:                         0.
% 3.96/1.01  sup_time_generating:                    0.
% 3.96/1.01  sup_time_sim_full:                      0.
% 3.96/1.01  sup_time_sim_immed:                     0.
% 3.96/1.01  
% 3.96/1.01  sup_num_of_clauses:                     330
% 3.96/1.01  sup_num_in_active:                      175
% 3.96/1.01  sup_num_in_passive:                     155
% 3.96/1.01  sup_num_of_loops:                       182
% 3.96/1.01  sup_fw_superposition:                   212
% 3.96/1.01  sup_bw_superposition:                   233
% 3.96/1.01  sup_immediate_simplified:               136
% 3.96/1.01  sup_given_eliminated:                   0
% 3.96/1.01  comparisons_done:                       0
% 3.96/1.01  comparisons_avoided:                    0
% 3.96/1.01  
% 3.96/1.01  ------ Simplifications
% 3.96/1.01  
% 3.96/1.01  
% 3.96/1.01  sim_fw_subset_subsumed:                 26
% 3.96/1.01  sim_bw_subset_subsumed:                 3
% 3.96/1.01  sim_fw_subsumed:                        28
% 3.96/1.01  sim_bw_subsumed:                        5
% 3.96/1.01  sim_fw_subsumption_res:                 8
% 3.96/1.01  sim_bw_subsumption_res:                 0
% 3.96/1.01  sim_tautology_del:                      13
% 3.96/1.01  sim_eq_tautology_del:                   18
% 3.96/1.01  sim_eq_res_simp:                        5
% 3.96/1.01  sim_fw_demodulated:                     7
% 3.96/1.01  sim_bw_demodulated:                     5
% 3.96/1.01  sim_light_normalised:                   91
% 3.96/1.01  sim_joinable_taut:                      0
% 3.96/1.01  sim_joinable_simp:                      0
% 3.96/1.01  sim_ac_normalised:                      0
% 3.96/1.01  sim_smt_subsumption:                    0
% 3.96/1.01  
%------------------------------------------------------------------------------
