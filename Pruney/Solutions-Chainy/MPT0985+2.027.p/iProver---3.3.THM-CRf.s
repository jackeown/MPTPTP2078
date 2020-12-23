%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:25 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  225 (10686 expanded)
%              Number of clauses        :  149 (3174 expanded)
%              Number of leaves         :   20 (2126 expanded)
%              Depth                    :   25
%              Number of atoms          :  707 (59419 expanded)
%              Number of equality atoms :  351 (11522 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f48,plain,(
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

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f51,plain,
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

fof(f52,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
      | ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
      | ~ v1_funct_1(k2_funct_1(sK5)) )
    & k2_relset_1(sK3,sK4,sK5) = sK4
    & v2_funct_1(sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f34,f51])).

fof(f89,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f90,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f52])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,(
    k2_relset_1(sK3,sK4,sK5) = sK4 ),
    inference(cnf_transformation,[],[f52])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f86,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f93,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
    | ~ v1_funct_1(k2_funct_1(sK5)) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f71,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,(
    v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f70,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f69,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f100,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f102,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f97,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_5570,plain,
    ( ~ r2_hidden(sK1(X0,k2_funct_1(sK5)),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5572,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,k2_funct_1(sK5)),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5570])).

cnf(c_3111,plain,
    ( ~ r2_hidden(sK1(X0,k2_zfmisc_1(X1,X2)),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5215,plain,
    ( ~ r2_hidden(sK1(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)),k2_funct_1(sK5))
    | ~ v1_xboole_0(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_3111])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_767,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X1
    | sK4 != X2
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_39])).

cnf(c_768,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_767])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_770,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_768,c_38])).

cnf(c_1716,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1722,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3721,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1716,c_1722])).

cnf(c_4079,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_770,c_3721])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1721,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3216,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1716,c_1721])).

cnf(c_36,negated_conjecture,
    ( k2_relset_1(sK3,sK4,sK5) = sK4 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3232,plain,
    ( k2_relat_1(sK5) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_3216,c_36])).

cnf(c_33,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_35,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
    | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_791,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relat_1(X0) != sK4
    | k2_relat_1(X0) != sK3
    | k2_funct_1(sK5) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_35])).

cnf(c_792,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_relat_1(k2_funct_1(sK5))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relat_1(k2_funct_1(sK5)) != sK4
    | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
    inference(unflattening,[status(thm)],[c_791])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_804,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relat_1(k2_funct_1(sK5)) != sK4
    | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_792,c_19])).

cnf(c_1703,plain,
    ( k1_relat_1(k2_funct_1(sK5)) != sK4
    | k2_relat_1(k2_funct_1(sK5)) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_37,negated_conjecture,
    ( v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_534,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_37])).

cnf(c_535,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_537,plain,
    ( ~ v1_relat_1(sK5)
    | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_40])).

cnf(c_1713,plain,
    ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_2045,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2050,plain,
    ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1713,c_40,c_38,c_535,c_2045])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_520,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_37])).

cnf(c_521,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_523,plain,
    ( ~ v1_relat_1(sK5)
    | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_521,c_40])).

cnf(c_1714,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_2054,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1714,c_40,c_38,c_521,c_2045])).

cnf(c_2111,plain,
    ( k1_relat_1(sK5) != sK3
    | k2_relat_1(sK5) != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1703,c_2050,c_2054])).

cnf(c_3263,plain,
    ( k1_relat_1(sK5) != sK3
    | sK4 != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3232,c_2111])).

cnf(c_3267,plain,
    ( k1_relat_1(sK5) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3263])).

cnf(c_41,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_43,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2046,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2045])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2147,plain,
    ( ~ v1_relat_1(sK5)
    | v1_funct_1(k2_funct_1(sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2148,plain,
    ( v1_relat_1(sK5) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2147])).

cnf(c_4242,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | k1_relat_1(sK5) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3267,c_41,c_43,c_2046,c_2111,c_2148,c_3232])).

cnf(c_4243,plain,
    ( k1_relat_1(sK5) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4242])).

cnf(c_4248,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4079,c_4243])).

cnf(c_32,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1717,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2756,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK5)),k1_relat_1(sK5)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2050,c_1717])).

cnf(c_2767,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK5),k1_relat_1(sK5)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK5)) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2756,c_2054])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2146,plain,
    ( v1_relat_1(k2_funct_1(sK5))
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2150,plain,
    ( v1_relat_1(k2_funct_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2146])).

cnf(c_3031,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK5),k1_relat_1(sK5)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2767,c_41,c_43,c_2046,c_2148,c_2150])).

cnf(c_3262,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k1_relat_1(sK5)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3232,c_3031])).

cnf(c_4086,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4079,c_3262])).

cnf(c_4258,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4248,c_4086])).

cnf(c_4272,plain,
    ( k2_relat_1(sK5) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4258,c_3232])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_603,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k2_relat_1(X2) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_604,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_603])).

cnf(c_620,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_604,c_19])).

cnf(c_1711,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1918,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1711,c_9])).

cnf(c_4962,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4272,c_1918])).

cnf(c_4282,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4258,c_1716])).

cnf(c_4287,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4282,c_9])).

cnf(c_5112,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4962,c_41,c_4287])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_661,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | X2 != X0
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_relat_1(X2) != k1_xboole_0
    | k2_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_33])).

cnf(c_662,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_676,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_662,c_19])).

cnf(c_1709,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1901,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1709,c_10])).

cnf(c_5117,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(sK5),sK5) = k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5112,c_1901])).

cnf(c_5140,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5117,c_4272])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X1
    | sK4 != k1_xboole_0
    | sK5 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_39])).

cnf(c_630,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | sK4 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_1710,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_1856,plain,
    ( sK3 = k1_xboole_0
    | sK4 != k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1710,c_9])).

cnf(c_4274,plain,
    ( sK3 = k1_xboole_0
    | sK5 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4258,c_1856])).

cnf(c_4325,plain,
    ( sK3 = k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4274])).

cnf(c_4329,plain,
    ( sK3 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4325,c_4287])).

cnf(c_4261,plain,
    ( k1_relat_1(sK5) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4258,c_4243])).

cnf(c_4376,plain,
    ( k1_relat_1(sK5) != sK3
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4261,c_10])).

cnf(c_4268,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK5)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4258,c_3262])).

cnf(c_4345,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4268,c_10])).

cnf(c_4790,plain,
    ( k1_relat_1(sK5) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4376,c_4345])).

cnf(c_5119,plain,
    ( sK3 != k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5112,c_4790])).

cnf(c_5147,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5140,c_4329,c_5119])).

cnf(c_891,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2212,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_891])).

cnf(c_5088,plain,
    ( k1_relat_1(k2_funct_1(sK5)) != X0
    | sK4 != X0
    | sK4 = k1_relat_1(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_2212])).

cnf(c_5092,plain,
    ( k1_relat_1(k2_funct_1(sK5)) != k1_xboole_0
    | sK4 = k1_relat_1(k2_funct_1(sK5))
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5088])).

cnf(c_810,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k2_funct_1(sK5) != sK5
    | sK3 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_39])).

cnf(c_1702,plain,
    ( k2_funct_1(sK5) != sK5
    | sK3 != sK4
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_810])).

cnf(c_4279,plain,
    ( k2_funct_1(sK5) != sK5
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4258,c_1702])).

cnf(c_4300,plain,
    ( k2_funct_1(sK5) != sK5
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4279,c_10])).

cnf(c_4348,plain,
    ( k2_funct_1(sK5) != sK5
    | sK3 != k1_xboole_0
    | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4345,c_4300])).

cnf(c_4384,plain,
    ( ~ v1_funct_1(k2_funct_1(sK5))
    | k2_funct_1(sK5) != sK5
    | sK3 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4348])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1727,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3036,plain,
    ( r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(k2_relat_1(sK5),k1_relat_1(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3031,c_1727])).

cnf(c_3261,plain,
    ( r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(sK4,k1_relat_1(sK5))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3232,c_3036])).

cnf(c_4269,plain,
    ( r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK5))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4258,c_3261])).

cnf(c_4342,plain,
    ( r1_tarski(k2_funct_1(sK5),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4269,c_10])).

cnf(c_4381,plain,
    ( r1_tarski(k2_funct_1(sK5),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4342])).

cnf(c_3264,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = sK4 ),
    inference(demodulation,[status(thm)],[c_3232,c_2054])).

cnf(c_4271,plain,
    ( k1_relat_1(k2_funct_1(sK5)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4258,c_3264])).

cnf(c_4230,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) = k1_relat_1(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3055,plain,
    ( k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != X0
    | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_891])).

cnf(c_4229,plain,
    ( k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != k1_relat_1(k2_funct_1(sK5))
    | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) = sK4
    | sK4 != k1_relat_1(k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_3055])).

cnf(c_2192,plain,
    ( X0 != X1
    | k2_funct_1(sK5) != X1
    | k2_funct_1(sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_891])).

cnf(c_3686,plain,
    ( k2_funct_1(sK5) != X0
    | k2_funct_1(sK5) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_2192])).

cnf(c_3690,plain,
    ( k2_funct_1(sK5) = sK5
    | k2_funct_1(sK5) != k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3686])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2253,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK1(X0,k2_zfmisc_1(X1,X2)),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2670,plain,
    ( r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3))
    | r2_hidden(sK1(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)),k2_funct_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_2253])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2040,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2522,plain,
    ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_2040])).

cnf(c_2412,plain,
    ( r1_tarski(X0,k2_funct_1(sK5))
    | r2_hidden(sK1(X0,k2_funct_1(sK5)),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2424,plain,
    ( r1_tarski(k1_xboole_0,k2_funct_1(sK5))
    | r2_hidden(sK1(k1_xboole_0,k2_funct_1(sK5)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2412])).

cnf(c_890,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2211,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_890])).

cnf(c_2082,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_891])).

cnf(c_2210,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2082])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2193,plain,
    ( ~ r1_tarski(X0,k2_funct_1(sK5))
    | ~ r1_tarski(k2_funct_1(sK5),X0)
    | k2_funct_1(sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2195,plain,
    ( ~ r1_tarski(k2_funct_1(sK5),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_funct_1(sK5))
    | k2_funct_1(sK5) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2193])).

cnf(c_892,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2169,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_funct_1(sK5))
    | k2_funct_1(sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_892])).

cnf(c_2171,plain,
    ( v1_xboole_0(k2_funct_1(sK5))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_funct_1(sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2169])).

cnf(c_25,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_751,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relset_1(X1,X2,X0) != X1
    | k2_funct_1(sK5) != X0
    | sK3 != X2
    | sK4 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_35])).

cnf(c_752,plain,
    ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    | ~ v1_funct_1(k2_funct_1(sK5))
    | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != sK4
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_751])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5572,c_5215,c_5147,c_5092,c_4384,c_4381,c_4271,c_4258,c_4230,c_4229,c_3690,c_2670,c_2522,c_2424,c_2211,c_2210,c_2195,c_2171,c_2147,c_2045,c_752,c_5,c_38,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.05/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/0.98  
% 3.05/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.05/0.98  
% 3.05/0.98  ------  iProver source info
% 3.05/0.98  
% 3.05/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.05/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.05/0.98  git: non_committed_changes: false
% 3.05/0.98  git: last_make_outside_of_git: false
% 3.05/0.98  
% 3.05/0.98  ------ 
% 3.05/0.98  
% 3.05/0.98  ------ Input Options
% 3.05/0.98  
% 3.05/0.98  --out_options                           all
% 3.05/0.98  --tptp_safe_out                         true
% 3.05/0.98  --problem_path                          ""
% 3.05/0.98  --include_path                          ""
% 3.05/0.98  --clausifier                            res/vclausify_rel
% 3.05/0.98  --clausifier_options                    --mode clausify
% 3.05/0.98  --stdin                                 false
% 3.05/0.98  --stats_out                             all
% 3.05/0.98  
% 3.05/0.98  ------ General Options
% 3.05/0.98  
% 3.05/0.98  --fof                                   false
% 3.05/0.98  --time_out_real                         305.
% 3.05/0.98  --time_out_virtual                      -1.
% 3.05/0.98  --symbol_type_check                     false
% 3.05/0.98  --clausify_out                          false
% 3.05/0.98  --sig_cnt_out                           false
% 3.05/0.98  --trig_cnt_out                          false
% 3.05/0.98  --trig_cnt_out_tolerance                1.
% 3.05/0.98  --trig_cnt_out_sk_spl                   false
% 3.05/0.98  --abstr_cl_out                          false
% 3.05/0.98  
% 3.05/0.98  ------ Global Options
% 3.05/0.98  
% 3.05/0.98  --schedule                              default
% 3.05/0.98  --add_important_lit                     false
% 3.05/0.98  --prop_solver_per_cl                    1000
% 3.05/0.98  --min_unsat_core                        false
% 3.05/0.98  --soft_assumptions                      false
% 3.05/0.98  --soft_lemma_size                       3
% 3.05/0.98  --prop_impl_unit_size                   0
% 3.05/0.98  --prop_impl_unit                        []
% 3.05/0.98  --share_sel_clauses                     true
% 3.05/0.98  --reset_solvers                         false
% 3.05/0.98  --bc_imp_inh                            [conj_cone]
% 3.05/0.98  --conj_cone_tolerance                   3.
% 3.05/0.98  --extra_neg_conj                        none
% 3.05/0.98  --large_theory_mode                     true
% 3.05/0.98  --prolific_symb_bound                   200
% 3.05/0.98  --lt_threshold                          2000
% 3.05/0.98  --clause_weak_htbl                      true
% 3.05/0.98  --gc_record_bc_elim                     false
% 3.05/0.98  
% 3.05/0.98  ------ Preprocessing Options
% 3.05/0.98  
% 3.05/0.98  --preprocessing_flag                    true
% 3.05/0.98  --time_out_prep_mult                    0.1
% 3.05/0.98  --splitting_mode                        input
% 3.05/0.98  --splitting_grd                         true
% 3.05/0.98  --splitting_cvd                         false
% 3.05/0.98  --splitting_cvd_svl                     false
% 3.05/0.98  --splitting_nvd                         32
% 3.05/0.98  --sub_typing                            true
% 3.05/0.98  --prep_gs_sim                           true
% 3.05/0.98  --prep_unflatten                        true
% 3.05/0.98  --prep_res_sim                          true
% 3.05/0.98  --prep_upred                            true
% 3.05/0.98  --prep_sem_filter                       exhaustive
% 3.05/0.98  --prep_sem_filter_out                   false
% 3.05/0.98  --pred_elim                             true
% 3.05/0.98  --res_sim_input                         true
% 3.05/0.98  --eq_ax_congr_red                       true
% 3.05/0.98  --pure_diseq_elim                       true
% 3.05/0.98  --brand_transform                       false
% 3.05/0.98  --non_eq_to_eq                          false
% 3.05/0.98  --prep_def_merge                        true
% 3.05/0.98  --prep_def_merge_prop_impl              false
% 3.05/0.98  --prep_def_merge_mbd                    true
% 3.05/0.98  --prep_def_merge_tr_red                 false
% 3.05/0.98  --prep_def_merge_tr_cl                  false
% 3.05/0.98  --smt_preprocessing                     true
% 3.05/0.98  --smt_ac_axioms                         fast
% 3.05/0.98  --preprocessed_out                      false
% 3.05/0.98  --preprocessed_stats                    false
% 3.05/0.98  
% 3.05/0.98  ------ Abstraction refinement Options
% 3.05/0.98  
% 3.05/0.98  --abstr_ref                             []
% 3.05/0.98  --abstr_ref_prep                        false
% 3.05/0.98  --abstr_ref_until_sat                   false
% 3.05/0.98  --abstr_ref_sig_restrict                funpre
% 3.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/0.98  --abstr_ref_under                       []
% 3.05/0.98  
% 3.05/0.98  ------ SAT Options
% 3.05/0.98  
% 3.05/0.98  --sat_mode                              false
% 3.05/0.98  --sat_fm_restart_options                ""
% 3.05/0.98  --sat_gr_def                            false
% 3.05/0.98  --sat_epr_types                         true
% 3.05/0.98  --sat_non_cyclic_types                  false
% 3.05/0.98  --sat_finite_models                     false
% 3.05/0.98  --sat_fm_lemmas                         false
% 3.05/0.98  --sat_fm_prep                           false
% 3.05/0.98  --sat_fm_uc_incr                        true
% 3.05/0.98  --sat_out_model                         small
% 3.05/0.98  --sat_out_clauses                       false
% 3.05/0.98  
% 3.05/0.98  ------ QBF Options
% 3.05/0.98  
% 3.05/0.98  --qbf_mode                              false
% 3.05/0.98  --qbf_elim_univ                         false
% 3.05/0.98  --qbf_dom_inst                          none
% 3.05/0.98  --qbf_dom_pre_inst                      false
% 3.05/0.98  --qbf_sk_in                             false
% 3.05/0.98  --qbf_pred_elim                         true
% 3.05/0.98  --qbf_split                             512
% 3.05/0.98  
% 3.05/0.98  ------ BMC1 Options
% 3.05/0.98  
% 3.05/0.98  --bmc1_incremental                      false
% 3.05/0.98  --bmc1_axioms                           reachable_all
% 3.05/0.98  --bmc1_min_bound                        0
% 3.05/0.98  --bmc1_max_bound                        -1
% 3.05/0.98  --bmc1_max_bound_default                -1
% 3.05/0.98  --bmc1_symbol_reachability              true
% 3.05/0.98  --bmc1_property_lemmas                  false
% 3.05/0.98  --bmc1_k_induction                      false
% 3.05/0.98  --bmc1_non_equiv_states                 false
% 3.05/0.98  --bmc1_deadlock                         false
% 3.05/0.98  --bmc1_ucm                              false
% 3.05/0.98  --bmc1_add_unsat_core                   none
% 3.05/0.98  --bmc1_unsat_core_children              false
% 3.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/0.98  --bmc1_out_stat                         full
% 3.05/0.98  --bmc1_ground_init                      false
% 3.05/0.98  --bmc1_pre_inst_next_state              false
% 3.05/0.98  --bmc1_pre_inst_state                   false
% 3.05/0.98  --bmc1_pre_inst_reach_state             false
% 3.05/0.98  --bmc1_out_unsat_core                   false
% 3.05/0.98  --bmc1_aig_witness_out                  false
% 3.05/0.98  --bmc1_verbose                          false
% 3.05/0.98  --bmc1_dump_clauses_tptp                false
% 3.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.05/0.98  --bmc1_dump_file                        -
% 3.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.05/0.98  --bmc1_ucm_extend_mode                  1
% 3.05/0.98  --bmc1_ucm_init_mode                    2
% 3.05/0.98  --bmc1_ucm_cone_mode                    none
% 3.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.05/0.98  --bmc1_ucm_relax_model                  4
% 3.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/0.98  --bmc1_ucm_layered_model                none
% 3.05/0.98  --bmc1_ucm_max_lemma_size               10
% 3.05/0.98  
% 3.05/0.98  ------ AIG Options
% 3.05/0.98  
% 3.05/0.98  --aig_mode                              false
% 3.05/0.98  
% 3.05/0.98  ------ Instantiation Options
% 3.05/0.98  
% 3.05/0.98  --instantiation_flag                    true
% 3.05/0.98  --inst_sos_flag                         false
% 3.05/0.98  --inst_sos_phase                        true
% 3.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/0.98  --inst_lit_sel_side                     num_symb
% 3.05/0.98  --inst_solver_per_active                1400
% 3.05/0.98  --inst_solver_calls_frac                1.
% 3.05/0.98  --inst_passive_queue_type               priority_queues
% 3.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/0.98  --inst_passive_queues_freq              [25;2]
% 3.05/0.98  --inst_dismatching                      true
% 3.05/0.98  --inst_eager_unprocessed_to_passive     true
% 3.05/0.98  --inst_prop_sim_given                   true
% 3.05/0.98  --inst_prop_sim_new                     false
% 3.05/0.98  --inst_subs_new                         false
% 3.05/0.99  --inst_eq_res_simp                      false
% 3.05/0.99  --inst_subs_given                       false
% 3.05/0.99  --inst_orphan_elimination               true
% 3.05/0.99  --inst_learning_loop_flag               true
% 3.05/0.99  --inst_learning_start                   3000
% 3.05/0.99  --inst_learning_factor                  2
% 3.05/0.99  --inst_start_prop_sim_after_learn       3
% 3.05/0.99  --inst_sel_renew                        solver
% 3.05/0.99  --inst_lit_activity_flag                true
% 3.05/0.99  --inst_restr_to_given                   false
% 3.05/0.99  --inst_activity_threshold               500
% 3.05/0.99  --inst_out_proof                        true
% 3.05/0.99  
% 3.05/0.99  ------ Resolution Options
% 3.05/0.99  
% 3.05/0.99  --resolution_flag                       true
% 3.05/0.99  --res_lit_sel                           adaptive
% 3.05/0.99  --res_lit_sel_side                      none
% 3.05/0.99  --res_ordering                          kbo
% 3.05/0.99  --res_to_prop_solver                    active
% 3.05/0.99  --res_prop_simpl_new                    false
% 3.05/0.99  --res_prop_simpl_given                  true
% 3.05/0.99  --res_passive_queue_type                priority_queues
% 3.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/0.99  --res_passive_queues_freq               [15;5]
% 3.05/0.99  --res_forward_subs                      full
% 3.05/0.99  --res_backward_subs                     full
% 3.05/0.99  --res_forward_subs_resolution           true
% 3.05/0.99  --res_backward_subs_resolution          true
% 3.05/0.99  --res_orphan_elimination                true
% 3.05/0.99  --res_time_limit                        2.
% 3.05/0.99  --res_out_proof                         true
% 3.05/0.99  
% 3.05/0.99  ------ Superposition Options
% 3.05/0.99  
% 3.05/0.99  --superposition_flag                    true
% 3.05/0.99  --sup_passive_queue_type                priority_queues
% 3.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.05/0.99  --demod_completeness_check              fast
% 3.05/0.99  --demod_use_ground                      true
% 3.05/0.99  --sup_to_prop_solver                    passive
% 3.05/0.99  --sup_prop_simpl_new                    true
% 3.05/0.99  --sup_prop_simpl_given                  true
% 3.05/0.99  --sup_fun_splitting                     false
% 3.05/0.99  --sup_smt_interval                      50000
% 3.05/0.99  
% 3.05/0.99  ------ Superposition Simplification Setup
% 3.05/0.99  
% 3.05/0.99  --sup_indices_passive                   []
% 3.05/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_full_bw                           [BwDemod]
% 3.05/0.99  --sup_immed_triv                        [TrivRules]
% 3.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_immed_bw_main                     []
% 3.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.99  
% 3.05/0.99  ------ Combination Options
% 3.05/0.99  
% 3.05/0.99  --comb_res_mult                         3
% 3.05/0.99  --comb_sup_mult                         2
% 3.05/0.99  --comb_inst_mult                        10
% 3.05/0.99  
% 3.05/0.99  ------ Debug Options
% 3.05/0.99  
% 3.05/0.99  --dbg_backtrace                         false
% 3.05/0.99  --dbg_dump_prop_clauses                 false
% 3.05/0.99  --dbg_dump_prop_clauses_file            -
% 3.05/0.99  --dbg_out_stat                          false
% 3.05/0.99  ------ Parsing...
% 3.05/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.05/0.99  
% 3.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.05/0.99  
% 3.05/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.05/0.99  
% 3.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.05/0.99  ------ Proving...
% 3.05/0.99  ------ Problem Properties 
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  clauses                                 43
% 3.05/0.99  conjectures                             3
% 3.05/0.99  EPR                                     7
% 3.05/0.99  Horn                                    34
% 3.05/0.99  unary                                   11
% 3.05/0.99  binary                                  15
% 3.05/0.99  lits                                    105
% 3.05/0.99  lits eq                                 42
% 3.05/0.99  fd_pure                                 0
% 3.05/0.99  fd_pseudo                               0
% 3.05/0.99  fd_cond                                 3
% 3.05/0.99  fd_pseudo_cond                          1
% 3.05/0.99  AC symbols                              0
% 3.05/0.99  
% 3.05/0.99  ------ Schedule dynamic 5 is on 
% 3.05/0.99  
% 3.05/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  ------ 
% 3.05/0.99  Current options:
% 3.05/0.99  ------ 
% 3.05/0.99  
% 3.05/0.99  ------ Input Options
% 3.05/0.99  
% 3.05/0.99  --out_options                           all
% 3.05/0.99  --tptp_safe_out                         true
% 3.05/0.99  --problem_path                          ""
% 3.05/0.99  --include_path                          ""
% 3.05/0.99  --clausifier                            res/vclausify_rel
% 3.05/0.99  --clausifier_options                    --mode clausify
% 3.05/0.99  --stdin                                 false
% 3.05/0.99  --stats_out                             all
% 3.05/0.99  
% 3.05/0.99  ------ General Options
% 3.05/0.99  
% 3.05/0.99  --fof                                   false
% 3.05/0.99  --time_out_real                         305.
% 3.05/0.99  --time_out_virtual                      -1.
% 3.05/0.99  --symbol_type_check                     false
% 3.05/0.99  --clausify_out                          false
% 3.05/0.99  --sig_cnt_out                           false
% 3.05/0.99  --trig_cnt_out                          false
% 3.05/0.99  --trig_cnt_out_tolerance                1.
% 3.05/0.99  --trig_cnt_out_sk_spl                   false
% 3.05/0.99  --abstr_cl_out                          false
% 3.05/0.99  
% 3.05/0.99  ------ Global Options
% 3.05/0.99  
% 3.05/0.99  --schedule                              default
% 3.05/0.99  --add_important_lit                     false
% 3.05/0.99  --prop_solver_per_cl                    1000
% 3.05/0.99  --min_unsat_core                        false
% 3.05/0.99  --soft_assumptions                      false
% 3.05/0.99  --soft_lemma_size                       3
% 3.05/0.99  --prop_impl_unit_size                   0
% 3.05/0.99  --prop_impl_unit                        []
% 3.05/0.99  --share_sel_clauses                     true
% 3.05/0.99  --reset_solvers                         false
% 3.05/0.99  --bc_imp_inh                            [conj_cone]
% 3.05/0.99  --conj_cone_tolerance                   3.
% 3.05/0.99  --extra_neg_conj                        none
% 3.05/0.99  --large_theory_mode                     true
% 3.05/0.99  --prolific_symb_bound                   200
% 3.05/0.99  --lt_threshold                          2000
% 3.05/0.99  --clause_weak_htbl                      true
% 3.05/0.99  --gc_record_bc_elim                     false
% 3.05/0.99  
% 3.05/0.99  ------ Preprocessing Options
% 3.05/0.99  
% 3.05/0.99  --preprocessing_flag                    true
% 3.05/0.99  --time_out_prep_mult                    0.1
% 3.05/0.99  --splitting_mode                        input
% 3.05/0.99  --splitting_grd                         true
% 3.05/0.99  --splitting_cvd                         false
% 3.05/0.99  --splitting_cvd_svl                     false
% 3.05/0.99  --splitting_nvd                         32
% 3.05/0.99  --sub_typing                            true
% 3.05/0.99  --prep_gs_sim                           true
% 3.05/0.99  --prep_unflatten                        true
% 3.05/0.99  --prep_res_sim                          true
% 3.05/0.99  --prep_upred                            true
% 3.05/0.99  --prep_sem_filter                       exhaustive
% 3.05/0.99  --prep_sem_filter_out                   false
% 3.05/0.99  --pred_elim                             true
% 3.05/0.99  --res_sim_input                         true
% 3.05/0.99  --eq_ax_congr_red                       true
% 3.05/0.99  --pure_diseq_elim                       true
% 3.05/0.99  --brand_transform                       false
% 3.05/0.99  --non_eq_to_eq                          false
% 3.05/0.99  --prep_def_merge                        true
% 3.05/0.99  --prep_def_merge_prop_impl              false
% 3.05/0.99  --prep_def_merge_mbd                    true
% 3.05/0.99  --prep_def_merge_tr_red                 false
% 3.05/0.99  --prep_def_merge_tr_cl                  false
% 3.05/0.99  --smt_preprocessing                     true
% 3.05/0.99  --smt_ac_axioms                         fast
% 3.05/0.99  --preprocessed_out                      false
% 3.05/0.99  --preprocessed_stats                    false
% 3.05/0.99  
% 3.05/0.99  ------ Abstraction refinement Options
% 3.05/0.99  
% 3.05/0.99  --abstr_ref                             []
% 3.05/0.99  --abstr_ref_prep                        false
% 3.05/0.99  --abstr_ref_until_sat                   false
% 3.05/0.99  --abstr_ref_sig_restrict                funpre
% 3.05/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/0.99  --abstr_ref_under                       []
% 3.05/0.99  
% 3.05/0.99  ------ SAT Options
% 3.05/0.99  
% 3.05/0.99  --sat_mode                              false
% 3.05/0.99  --sat_fm_restart_options                ""
% 3.05/0.99  --sat_gr_def                            false
% 3.05/0.99  --sat_epr_types                         true
% 3.05/0.99  --sat_non_cyclic_types                  false
% 3.05/0.99  --sat_finite_models                     false
% 3.05/0.99  --sat_fm_lemmas                         false
% 3.05/0.99  --sat_fm_prep                           false
% 3.05/0.99  --sat_fm_uc_incr                        true
% 3.05/0.99  --sat_out_model                         small
% 3.05/0.99  --sat_out_clauses                       false
% 3.05/0.99  
% 3.05/0.99  ------ QBF Options
% 3.05/0.99  
% 3.05/0.99  --qbf_mode                              false
% 3.05/0.99  --qbf_elim_univ                         false
% 3.05/0.99  --qbf_dom_inst                          none
% 3.05/0.99  --qbf_dom_pre_inst                      false
% 3.05/0.99  --qbf_sk_in                             false
% 3.05/0.99  --qbf_pred_elim                         true
% 3.05/0.99  --qbf_split                             512
% 3.05/0.99  
% 3.05/0.99  ------ BMC1 Options
% 3.05/0.99  
% 3.05/0.99  --bmc1_incremental                      false
% 3.05/0.99  --bmc1_axioms                           reachable_all
% 3.05/0.99  --bmc1_min_bound                        0
% 3.05/0.99  --bmc1_max_bound                        -1
% 3.05/0.99  --bmc1_max_bound_default                -1
% 3.05/0.99  --bmc1_symbol_reachability              true
% 3.05/0.99  --bmc1_property_lemmas                  false
% 3.05/0.99  --bmc1_k_induction                      false
% 3.05/0.99  --bmc1_non_equiv_states                 false
% 3.05/0.99  --bmc1_deadlock                         false
% 3.05/0.99  --bmc1_ucm                              false
% 3.05/0.99  --bmc1_add_unsat_core                   none
% 3.05/0.99  --bmc1_unsat_core_children              false
% 3.05/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/0.99  --bmc1_out_stat                         full
% 3.05/0.99  --bmc1_ground_init                      false
% 3.05/0.99  --bmc1_pre_inst_next_state              false
% 3.05/0.99  --bmc1_pre_inst_state                   false
% 3.05/0.99  --bmc1_pre_inst_reach_state             false
% 3.05/0.99  --bmc1_out_unsat_core                   false
% 3.05/0.99  --bmc1_aig_witness_out                  false
% 3.05/0.99  --bmc1_verbose                          false
% 3.05/0.99  --bmc1_dump_clauses_tptp                false
% 3.05/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.05/0.99  --bmc1_dump_file                        -
% 3.05/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.05/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.05/0.99  --bmc1_ucm_extend_mode                  1
% 3.05/0.99  --bmc1_ucm_init_mode                    2
% 3.05/0.99  --bmc1_ucm_cone_mode                    none
% 3.05/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.05/0.99  --bmc1_ucm_relax_model                  4
% 3.05/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.05/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/0.99  --bmc1_ucm_layered_model                none
% 3.05/0.99  --bmc1_ucm_max_lemma_size               10
% 3.05/0.99  
% 3.05/0.99  ------ AIG Options
% 3.05/0.99  
% 3.05/0.99  --aig_mode                              false
% 3.05/0.99  
% 3.05/0.99  ------ Instantiation Options
% 3.05/0.99  
% 3.05/0.99  --instantiation_flag                    true
% 3.05/0.99  --inst_sos_flag                         false
% 3.05/0.99  --inst_sos_phase                        true
% 3.05/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/0.99  --inst_lit_sel_side                     none
% 3.05/0.99  --inst_solver_per_active                1400
% 3.05/0.99  --inst_solver_calls_frac                1.
% 3.05/0.99  --inst_passive_queue_type               priority_queues
% 3.05/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/0.99  --inst_passive_queues_freq              [25;2]
% 3.05/0.99  --inst_dismatching                      true
% 3.05/0.99  --inst_eager_unprocessed_to_passive     true
% 3.05/0.99  --inst_prop_sim_given                   true
% 3.05/0.99  --inst_prop_sim_new                     false
% 3.05/0.99  --inst_subs_new                         false
% 3.05/0.99  --inst_eq_res_simp                      false
% 3.05/0.99  --inst_subs_given                       false
% 3.05/0.99  --inst_orphan_elimination               true
% 3.05/0.99  --inst_learning_loop_flag               true
% 3.05/0.99  --inst_learning_start                   3000
% 3.05/0.99  --inst_learning_factor                  2
% 3.05/0.99  --inst_start_prop_sim_after_learn       3
% 3.05/0.99  --inst_sel_renew                        solver
% 3.05/0.99  --inst_lit_activity_flag                true
% 3.05/0.99  --inst_restr_to_given                   false
% 3.05/0.99  --inst_activity_threshold               500
% 3.05/0.99  --inst_out_proof                        true
% 3.05/0.99  
% 3.05/0.99  ------ Resolution Options
% 3.05/0.99  
% 3.05/0.99  --resolution_flag                       false
% 3.05/0.99  --res_lit_sel                           adaptive
% 3.05/0.99  --res_lit_sel_side                      none
% 3.05/0.99  --res_ordering                          kbo
% 3.05/0.99  --res_to_prop_solver                    active
% 3.05/0.99  --res_prop_simpl_new                    false
% 3.05/0.99  --res_prop_simpl_given                  true
% 3.05/0.99  --res_passive_queue_type                priority_queues
% 3.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/0.99  --res_passive_queues_freq               [15;5]
% 3.05/0.99  --res_forward_subs                      full
% 3.05/0.99  --res_backward_subs                     full
% 3.05/0.99  --res_forward_subs_resolution           true
% 3.05/0.99  --res_backward_subs_resolution          true
% 3.05/0.99  --res_orphan_elimination                true
% 3.05/0.99  --res_time_limit                        2.
% 3.05/0.99  --res_out_proof                         true
% 3.05/0.99  
% 3.05/0.99  ------ Superposition Options
% 3.05/0.99  
% 3.05/0.99  --superposition_flag                    true
% 3.05/0.99  --sup_passive_queue_type                priority_queues
% 3.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.05/0.99  --demod_completeness_check              fast
% 3.05/0.99  --demod_use_ground                      true
% 3.05/0.99  --sup_to_prop_solver                    passive
% 3.05/0.99  --sup_prop_simpl_new                    true
% 3.05/0.99  --sup_prop_simpl_given                  true
% 3.05/0.99  --sup_fun_splitting                     false
% 3.05/0.99  --sup_smt_interval                      50000
% 3.05/0.99  
% 3.05/0.99  ------ Superposition Simplification Setup
% 3.05/0.99  
% 3.05/0.99  --sup_indices_passive                   []
% 3.05/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_full_bw                           [BwDemod]
% 3.05/0.99  --sup_immed_triv                        [TrivRules]
% 3.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_immed_bw_main                     []
% 3.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.99  
% 3.05/0.99  ------ Combination Options
% 3.05/0.99  
% 3.05/0.99  --comb_res_mult                         3
% 3.05/0.99  --comb_sup_mult                         2
% 3.05/0.99  --comb_inst_mult                        10
% 3.05/0.99  
% 3.05/0.99  ------ Debug Options
% 3.05/0.99  
% 3.05/0.99  --dbg_backtrace                         false
% 3.05/0.99  --dbg_dump_prop_clauses                 false
% 3.05/0.99  --dbg_dump_prop_clauses_file            -
% 3.05/0.99  --dbg_out_stat                          false
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  ------ Proving...
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  % SZS status Theorem for theBenchmark.p
% 3.05/0.99  
% 3.05/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.05/0.99  
% 3.05/0.99  fof(f1,axiom,(
% 3.05/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f35,plain,(
% 3.05/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.05/0.99    inference(nnf_transformation,[],[f1])).
% 3.05/0.99  
% 3.05/0.99  fof(f36,plain,(
% 3.05/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.05/0.99    inference(rectify,[],[f35])).
% 3.05/0.99  
% 3.05/0.99  fof(f37,plain,(
% 3.05/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.05/0.99    introduced(choice_axiom,[])).
% 3.05/0.99  
% 3.05/0.99  fof(f38,plain,(
% 3.05/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.05/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 3.05/0.99  
% 3.05/0.99  fof(f53,plain,(
% 3.05/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f38])).
% 3.05/0.99  
% 3.05/0.99  fof(f13,axiom,(
% 3.05/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f29,plain,(
% 3.05/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.99    inference(ennf_transformation,[],[f13])).
% 3.05/0.99  
% 3.05/0.99  fof(f30,plain,(
% 3.05/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.99    inference(flattening,[],[f29])).
% 3.05/0.99  
% 3.05/0.99  fof(f48,plain,(
% 3.05/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.99    inference(nnf_transformation,[],[f30])).
% 3.05/0.99  
% 3.05/0.99  fof(f75,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f48])).
% 3.05/0.99  
% 3.05/0.99  fof(f16,conjecture,(
% 3.05/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f17,negated_conjecture,(
% 3.05/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.05/0.99    inference(negated_conjecture,[],[f16])).
% 3.05/0.99  
% 3.05/0.99  fof(f33,plain,(
% 3.05/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.05/0.99    inference(ennf_transformation,[],[f17])).
% 3.05/0.99  
% 3.05/0.99  fof(f34,plain,(
% 3.05/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.05/0.99    inference(flattening,[],[f33])).
% 3.05/0.99  
% 3.05/0.99  fof(f51,plain,(
% 3.05/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) | ~v1_funct_2(k2_funct_1(sK5),sK4,sK3) | ~v1_funct_1(k2_funct_1(sK5))) & k2_relset_1(sK3,sK4,sK5) = sK4 & v2_funct_1(sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 3.05/0.99    introduced(choice_axiom,[])).
% 3.05/0.99  
% 3.05/0.99  fof(f52,plain,(
% 3.05/0.99    (~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) | ~v1_funct_2(k2_funct_1(sK5),sK4,sK3) | ~v1_funct_1(k2_funct_1(sK5))) & k2_relset_1(sK3,sK4,sK5) = sK4 & v2_funct_1(sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 3.05/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f34,f51])).
% 3.05/0.99  
% 3.05/0.99  fof(f89,plain,(
% 3.05/0.99    v1_funct_2(sK5,sK3,sK4)),
% 3.05/0.99    inference(cnf_transformation,[],[f52])).
% 3.05/0.99  
% 3.05/0.99  fof(f90,plain,(
% 3.05/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.05/0.99    inference(cnf_transformation,[],[f52])).
% 3.05/0.99  
% 3.05/0.99  fof(f11,axiom,(
% 3.05/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f27,plain,(
% 3.05/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.99    inference(ennf_transformation,[],[f11])).
% 3.05/0.99  
% 3.05/0.99  fof(f73,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f27])).
% 3.05/0.99  
% 3.05/0.99  fof(f12,axiom,(
% 3.05/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f28,plain,(
% 3.05/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.99    inference(ennf_transformation,[],[f12])).
% 3.05/0.99  
% 3.05/0.99  fof(f74,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f28])).
% 3.05/0.99  
% 3.05/0.99  fof(f92,plain,(
% 3.05/0.99    k2_relset_1(sK3,sK4,sK5) = sK4),
% 3.05/0.99    inference(cnf_transformation,[],[f52])).
% 3.05/0.99  
% 3.05/0.99  fof(f15,axiom,(
% 3.05/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f31,plain,(
% 3.05/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.05/0.99    inference(ennf_transformation,[],[f15])).
% 3.05/0.99  
% 3.05/0.99  fof(f32,plain,(
% 3.05/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.05/0.99    inference(flattening,[],[f31])).
% 3.05/0.99  
% 3.05/0.99  fof(f86,plain,(
% 3.05/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f32])).
% 3.05/0.99  
% 3.05/0.99  fof(f93,plain,(
% 3.05/0.99    ~m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) | ~v1_funct_2(k2_funct_1(sK5),sK4,sK3) | ~v1_funct_1(k2_funct_1(sK5))),
% 3.05/0.99    inference(cnf_transformation,[],[f52])).
% 3.05/0.99  
% 3.05/0.99  fof(f10,axiom,(
% 3.05/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f26,plain,(
% 3.05/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.99    inference(ennf_transformation,[],[f10])).
% 3.05/0.99  
% 3.05/0.99  fof(f72,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f26])).
% 3.05/0.99  
% 3.05/0.99  fof(f9,axiom,(
% 3.05/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f24,plain,(
% 3.05/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.05/0.99    inference(ennf_transformation,[],[f9])).
% 3.05/0.99  
% 3.05/0.99  fof(f25,plain,(
% 3.05/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.05/0.99    inference(flattening,[],[f24])).
% 3.05/0.99  
% 3.05/0.99  fof(f71,plain,(
% 3.05/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f25])).
% 3.05/0.99  
% 3.05/0.99  fof(f91,plain,(
% 3.05/0.99    v2_funct_1(sK5)),
% 3.05/0.99    inference(cnf_transformation,[],[f52])).
% 3.05/0.99  
% 3.05/0.99  fof(f88,plain,(
% 3.05/0.99    v1_funct_1(sK5)),
% 3.05/0.99    inference(cnf_transformation,[],[f52])).
% 3.05/0.99  
% 3.05/0.99  fof(f70,plain,(
% 3.05/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f25])).
% 3.05/0.99  
% 3.05/0.99  fof(f8,axiom,(
% 3.05/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f22,plain,(
% 3.05/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.05/0.99    inference(ennf_transformation,[],[f8])).
% 3.05/0.99  
% 3.05/0.99  fof(f23,plain,(
% 3.05/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.05/0.99    inference(flattening,[],[f22])).
% 3.05/0.99  
% 3.05/0.99  fof(f69,plain,(
% 3.05/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f23])).
% 3.05/0.99  
% 3.05/0.99  fof(f87,plain,(
% 3.05/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f32])).
% 3.05/0.99  
% 3.05/0.99  fof(f68,plain,(
% 3.05/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f23])).
% 3.05/0.99  
% 3.05/0.99  fof(f79,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f48])).
% 3.05/0.99  
% 3.05/0.99  fof(f100,plain,(
% 3.05/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.05/0.99    inference(equality_resolution,[],[f79])).
% 3.05/0.99  
% 3.05/0.99  fof(f5,axiom,(
% 3.05/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f45,plain,(
% 3.05/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.05/0.99    inference(nnf_transformation,[],[f5])).
% 3.05/0.99  
% 3.05/0.99  fof(f46,plain,(
% 3.05/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.05/0.99    inference(flattening,[],[f45])).
% 3.05/0.99  
% 3.05/0.99  fof(f64,plain,(
% 3.05/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.05/0.99    inference(cnf_transformation,[],[f46])).
% 3.05/0.99  
% 3.05/0.99  fof(f96,plain,(
% 3.05/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.05/0.99    inference(equality_resolution,[],[f64])).
% 3.05/0.99  
% 3.05/0.99  fof(f76,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f48])).
% 3.05/0.99  
% 3.05/0.99  fof(f102,plain,(
% 3.05/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.05/0.99    inference(equality_resolution,[],[f76])).
% 3.05/0.99  
% 3.05/0.99  fof(f63,plain,(
% 3.05/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.05/0.99    inference(cnf_transformation,[],[f46])).
% 3.05/0.99  
% 3.05/0.99  fof(f97,plain,(
% 3.05/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.05/0.99    inference(equality_resolution,[],[f63])).
% 3.05/0.99  
% 3.05/0.99  fof(f6,axiom,(
% 3.05/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f47,plain,(
% 3.05/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.05/0.99    inference(nnf_transformation,[],[f6])).
% 3.05/0.99  
% 3.05/0.99  fof(f65,plain,(
% 3.05/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f47])).
% 3.05/0.99  
% 3.05/0.99  fof(f2,axiom,(
% 3.05/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f20,plain,(
% 3.05/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.05/0.99    inference(ennf_transformation,[],[f2])).
% 3.05/0.99  
% 3.05/0.99  fof(f39,plain,(
% 3.05/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.05/0.99    inference(nnf_transformation,[],[f20])).
% 3.05/0.99  
% 3.05/0.99  fof(f40,plain,(
% 3.05/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.05/0.99    inference(rectify,[],[f39])).
% 3.05/0.99  
% 3.05/0.99  fof(f41,plain,(
% 3.05/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.05/0.99    introduced(choice_axiom,[])).
% 3.05/0.99  
% 3.05/0.99  fof(f42,plain,(
% 3.05/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.05/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).
% 3.05/0.99  
% 3.05/0.99  fof(f56,plain,(
% 3.05/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f42])).
% 3.05/0.99  
% 3.05/0.99  fof(f66,plain,(
% 3.05/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f47])).
% 3.05/0.99  
% 3.05/0.99  fof(f4,axiom,(
% 3.05/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f43,plain,(
% 3.05/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.05/0.99    inference(nnf_transformation,[],[f4])).
% 3.05/0.99  
% 3.05/0.99  fof(f44,plain,(
% 3.05/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.05/0.99    inference(flattening,[],[f43])).
% 3.05/0.99  
% 3.05/0.99  fof(f61,plain,(
% 3.05/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.05/0.99    inference(cnf_transformation,[],[f44])).
% 3.05/0.99  
% 3.05/0.99  fof(f77,plain,(
% 3.05/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.99    inference(cnf_transformation,[],[f48])).
% 3.05/0.99  
% 3.05/0.99  fof(f3,axiom,(
% 3.05/0.99    v1_xboole_0(k1_xboole_0)),
% 3.05/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.05/0.99  
% 3.05/0.99  fof(f58,plain,(
% 3.05/0.99    v1_xboole_0(k1_xboole_0)),
% 3.05/0.99    inference(cnf_transformation,[],[f3])).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1,plain,
% 3.05/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.05/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5570,plain,
% 3.05/0.99      ( ~ r2_hidden(sK1(X0,k2_funct_1(sK5)),X0) | ~ v1_xboole_0(X0) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5572,plain,
% 3.05/0.99      ( ~ r2_hidden(sK1(k1_xboole_0,k2_funct_1(sK5)),k1_xboole_0)
% 3.05/0.99      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_5570]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3111,plain,
% 3.05/0.99      ( ~ r2_hidden(sK1(X0,k2_zfmisc_1(X1,X2)),X0) | ~ v1_xboole_0(X0) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5215,plain,
% 3.05/0.99      ( ~ r2_hidden(sK1(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)),k2_funct_1(sK5))
% 3.05/0.99      | ~ v1_xboole_0(k2_funct_1(sK5)) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_3111]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_27,plain,
% 3.05/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.05/0.99      | k1_xboole_0 = X2 ),
% 3.05/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_39,negated_conjecture,
% 3.05/0.99      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.05/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_767,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.05/0.99      | sK3 != X1
% 3.05/0.99      | sK4 != X2
% 3.05/0.99      | sK5 != X0
% 3.05/0.99      | k1_xboole_0 = X2 ),
% 3.05/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_39]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_768,plain,
% 3.05/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.05/0.99      | k1_relset_1(sK3,sK4,sK5) = sK3
% 3.05/0.99      | k1_xboole_0 = sK4 ),
% 3.05/0.99      inference(unflattening,[status(thm)],[c_767]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_38,negated_conjecture,
% 3.05/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.05/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_770,plain,
% 3.05/0.99      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_768,c_38]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1716,plain,
% 3.05/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_20,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1722,plain,
% 3.05/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.05/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3721,plain,
% 3.05/0.99      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_1716,c_1722]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4079,plain,
% 3.05/0.99      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_770,c_3721]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_21,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1721,plain,
% 3.05/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.05/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3216,plain,
% 3.05/0.99      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_1716,c_1721]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_36,negated_conjecture,
% 3.05/0.99      ( k2_relset_1(sK3,sK4,sK5) = sK4 ),
% 3.05/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3232,plain,
% 3.05/0.99      ( k2_relat_1(sK5) = sK4 ),
% 3.05/0.99      inference(light_normalisation,[status(thm)],[c_3216,c_36]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_33,plain,
% 3.05/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.05/0.99      | ~ v1_relat_1(X0)
% 3.05/0.99      | ~ v1_funct_1(X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_35,negated_conjecture,
% 3.05/0.99      ( ~ v1_funct_2(k2_funct_1(sK5),sK4,sK3)
% 3.05/0.99      | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.05/0.99      | ~ v1_funct_1(k2_funct_1(sK5)) ),
% 3.05/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_791,plain,
% 3.05/0.99      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.05/0.99      | ~ v1_relat_1(X0)
% 3.05/0.99      | ~ v1_funct_1(X0)
% 3.05/0.99      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.05/0.99      | k1_relat_1(X0) != sK4
% 3.05/0.99      | k2_relat_1(X0) != sK3
% 3.05/0.99      | k2_funct_1(sK5) != X0 ),
% 3.05/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_35]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_792,plain,
% 3.05/0.99      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.05/0.99      | ~ v1_relat_1(k2_funct_1(sK5))
% 3.05/0.99      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.05/0.99      | k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.05/0.99      | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
% 3.05/0.99      inference(unflattening,[status(thm)],[c_791]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_19,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.99      | v1_relat_1(X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_804,plain,
% 3.05/0.99      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.05/0.99      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.05/0.99      | k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.05/0.99      | k2_relat_1(k2_funct_1(sK5)) != sK3 ),
% 3.05/0.99      inference(forward_subsumption_resolution,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_792,c_19]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1703,plain,
% 3.05/0.99      ( k1_relat_1(k2_funct_1(sK5)) != sK4
% 3.05/0.99      | k2_relat_1(k2_funct_1(sK5)) != sK3
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_17,plain,
% 3.05/0.99      ( ~ v2_funct_1(X0)
% 3.05/0.99      | ~ v1_relat_1(X0)
% 3.05/0.99      | ~ v1_funct_1(X0)
% 3.05/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_37,negated_conjecture,
% 3.05/0.99      ( v2_funct_1(sK5) ),
% 3.05/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_534,plain,
% 3.05/0.99      ( ~ v1_relat_1(X0)
% 3.05/0.99      | ~ v1_funct_1(X0)
% 3.05/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.05/0.99      | sK5 != X0 ),
% 3.05/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_37]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_535,plain,
% 3.05/0.99      ( ~ v1_relat_1(sK5)
% 3.05/0.99      | ~ v1_funct_1(sK5)
% 3.05/0.99      | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
% 3.05/0.99      inference(unflattening,[status(thm)],[c_534]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_40,negated_conjecture,
% 3.05/0.99      ( v1_funct_1(sK5) ),
% 3.05/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_537,plain,
% 3.05/0.99      ( ~ v1_relat_1(sK5)
% 3.05/0.99      | k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_535,c_40]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1713,plain,
% 3.05/0.99      ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5)
% 3.05/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2045,plain,
% 3.05/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.05/0.99      | v1_relat_1(sK5) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2050,plain,
% 3.05/0.99      ( k2_relat_1(k2_funct_1(sK5)) = k1_relat_1(sK5) ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_1713,c_40,c_38,c_535,c_2045]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_18,plain,
% 3.05/0.99      ( ~ v2_funct_1(X0)
% 3.05/0.99      | ~ v1_relat_1(X0)
% 3.05/0.99      | ~ v1_funct_1(X0)
% 3.05/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_520,plain,
% 3.05/0.99      ( ~ v1_relat_1(X0)
% 3.05/0.99      | ~ v1_funct_1(X0)
% 3.05/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.05/0.99      | sK5 != X0 ),
% 3.05/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_37]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_521,plain,
% 3.05/0.99      ( ~ v1_relat_1(sK5)
% 3.05/0.99      | ~ v1_funct_1(sK5)
% 3.05/0.99      | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
% 3.05/0.99      inference(unflattening,[status(thm)],[c_520]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_523,plain,
% 3.05/0.99      ( ~ v1_relat_1(sK5)
% 3.05/0.99      | k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_521,c_40]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1714,plain,
% 3.05/0.99      ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5)
% 3.05/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2054,plain,
% 3.05/0.99      ( k1_relat_1(k2_funct_1(sK5)) = k2_relat_1(sK5) ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_1714,c_40,c_38,c_521,c_2045]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2111,plain,
% 3.05/0.99      ( k1_relat_1(sK5) != sK3
% 3.05/0.99      | k2_relat_1(sK5) != sK4
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.05/0.99      inference(light_normalisation,[status(thm)],[c_1703,c_2050,c_2054]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3263,plain,
% 3.05/0.99      ( k1_relat_1(sK5) != sK3
% 3.05/0.99      | sK4 != sK4
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_3232,c_2111]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3267,plain,
% 3.05/0.99      ( k1_relat_1(sK5) != sK3
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.05/0.99      inference(equality_resolution_simp,[status(thm)],[c_3263]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_41,plain,
% 3.05/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_43,plain,
% 3.05/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2046,plain,
% 3.05/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.05/0.99      | v1_relat_1(sK5) = iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_2045]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_15,plain,
% 3.05/0.99      ( ~ v1_relat_1(X0)
% 3.05/0.99      | ~ v1_funct_1(X0)
% 3.05/0.99      | v1_funct_1(k2_funct_1(X0)) ),
% 3.05/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2147,plain,
% 3.05/0.99      ( ~ v1_relat_1(sK5)
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK5))
% 3.05/0.99      | ~ v1_funct_1(sK5) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2148,plain,
% 3.05/0.99      ( v1_relat_1(sK5) != iProver_top
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK5)) = iProver_top
% 3.05/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_2147]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4242,plain,
% 3.05/0.99      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.05/0.99      | k1_relat_1(sK5) != sK3 ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_3267,c_41,c_43,c_2046,c_2111,c_2148,c_3232]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4243,plain,
% 3.05/0.99      ( k1_relat_1(sK5) != sK3
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.05/0.99      inference(renaming,[status(thm)],[c_4242]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4248,plain,
% 3.05/0.99      ( sK4 = k1_xboole_0
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_4079,c_4243]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_32,plain,
% 3.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.05/0.99      | ~ v1_relat_1(X0)
% 3.05/0.99      | ~ v1_funct_1(X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1717,plain,
% 3.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.05/0.99      | v1_relat_1(X0) != iProver_top
% 3.05/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2756,plain,
% 3.05/0.99      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK5)),k1_relat_1(sK5)))) = iProver_top
% 3.05/0.99      | v1_relat_1(k2_funct_1(sK5)) != iProver_top
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_2050,c_1717]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2767,plain,
% 3.05/0.99      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK5),k1_relat_1(sK5)))) = iProver_top
% 3.05/0.99      | v1_relat_1(k2_funct_1(sK5)) != iProver_top
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.05/0.99      inference(light_normalisation,[status(thm)],[c_2756,c_2054]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_16,plain,
% 3.05/0.99      ( ~ v1_relat_1(X0)
% 3.05/0.99      | v1_relat_1(k2_funct_1(X0))
% 3.05/0.99      | ~ v1_funct_1(X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2146,plain,
% 3.05/0.99      ( v1_relat_1(k2_funct_1(sK5))
% 3.05/0.99      | ~ v1_relat_1(sK5)
% 3.05/0.99      | ~ v1_funct_1(sK5) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2150,plain,
% 3.05/0.99      ( v1_relat_1(k2_funct_1(sK5)) = iProver_top
% 3.05/0.99      | v1_relat_1(sK5) != iProver_top
% 3.05/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_2146]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3031,plain,
% 3.05/0.99      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK5),k1_relat_1(sK5)))) = iProver_top ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_2767,c_41,c_43,c_2046,c_2148,c_2150]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3262,plain,
% 3.05/0.99      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,k1_relat_1(sK5)))) = iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_3232,c_3031]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4086,plain,
% 3.05/0.99      ( sK4 = k1_xboole_0
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_4079,c_3262]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4258,plain,
% 3.05/0.99      ( sK4 = k1_xboole_0 ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_4248,c_4086]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4272,plain,
% 3.05/0.99      ( k2_relat_1(sK5) = k1_xboole_0 ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4258,c_3232]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_23,plain,
% 3.05/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.05/0.99      | k1_xboole_0 = X1
% 3.05/0.99      | k1_xboole_0 = X0 ),
% 3.05/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_603,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.05/0.99      | ~ v1_relat_1(X2)
% 3.05/0.99      | ~ v1_funct_1(X2)
% 3.05/0.99      | X2 != X0
% 3.05/0.99      | k1_relat_1(X2) != X1
% 3.05/0.99      | k2_relat_1(X2) != k1_xboole_0
% 3.05/0.99      | k1_xboole_0 = X0
% 3.05/0.99      | k1_xboole_0 = X1 ),
% 3.05/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_604,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.05/0.99      | ~ v1_relat_1(X0)
% 3.05/0.99      | ~ v1_funct_1(X0)
% 3.05/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.05/0.99      | k1_xboole_0 = X0
% 3.05/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.05/0.99      inference(unflattening,[status(thm)],[c_603]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_620,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.05/0.99      | ~ v1_funct_1(X0)
% 3.05/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.05/0.99      | k1_xboole_0 = X0
% 3.05/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.05/0.99      inference(forward_subsumption_resolution,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_604,c_19]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1711,plain,
% 3.05/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.05/0.99      | k1_xboole_0 = X0
% 3.05/0.99      | k1_xboole_0 = k1_relat_1(X0)
% 3.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
% 3.05/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_9,plain,
% 3.05/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.05/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1918,plain,
% 3.05/0.99      ( k1_relat_1(X0) = k1_xboole_0
% 3.05/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.05/0.99      | k1_xboole_0 = X0
% 3.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.05/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_1711,c_9]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4962,plain,
% 3.05/0.99      ( k1_relat_1(sK5) = k1_xboole_0
% 3.05/0.99      | sK5 = k1_xboole_0
% 3.05/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.05/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_4272,c_1918]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4282,plain,
% 3.05/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4258,c_1716]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4287,plain,
% 3.05/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4282,c_9]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5112,plain,
% 3.05/0.99      ( k1_relat_1(sK5) = k1_xboole_0 | sK5 = k1_xboole_0 ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_4962,c_41,c_4287]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_26,plain,
% 3.05/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.05/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.05/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_661,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.05/0.99      | ~ v1_relat_1(X2)
% 3.05/0.99      | ~ v1_funct_1(X2)
% 3.05/0.99      | X2 != X0
% 3.05/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.05/0.99      | k1_relat_1(X2) != k1_xboole_0
% 3.05/0.99      | k2_relat_1(X2) != X1 ),
% 3.05/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_33]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_662,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
% 3.05/0.99      | ~ v1_relat_1(X0)
% 3.05/0.99      | ~ v1_funct_1(X0)
% 3.05/0.99      | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 3.05/0.99      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.05/0.99      inference(unflattening,[status(thm)],[c_661]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_676,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
% 3.05/0.99      | ~ v1_funct_1(X0)
% 3.05/0.99      | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 3.05/0.99      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.05/0.99      inference(forward_subsumption_resolution,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_662,c_19]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1709,plain,
% 3.05/0.99      ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 3.05/0.99      | k1_relat_1(X0) != k1_xboole_0
% 3.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0)))) != iProver_top
% 3.05/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_10,plain,
% 3.05/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.05/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1901,plain,
% 3.05/0.99      ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 3.05/0.99      | k1_relat_1(X0) != k1_xboole_0
% 3.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.05/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_1709,c_10]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5117,plain,
% 3.05/0.99      ( k1_relset_1(k1_xboole_0,k2_relat_1(sK5),sK5) = k1_xboole_0
% 3.05/0.99      | sK5 = k1_xboole_0
% 3.05/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.05/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_5112,c_1901]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5140,plain,
% 3.05/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 3.05/0.99      | sK5 = k1_xboole_0
% 3.05/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.05/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.05/0.99      inference(light_normalisation,[status(thm)],[c_5117,c_4272]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_629,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.05/0.99      | sK3 != X1
% 3.05/0.99      | sK4 != k1_xboole_0
% 3.05/0.99      | sK5 != X0
% 3.05/0.99      | k1_xboole_0 = X0
% 3.05/0.99      | k1_xboole_0 = X1 ),
% 3.05/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_39]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_630,plain,
% 3.05/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
% 3.05/0.99      | sK4 != k1_xboole_0
% 3.05/0.99      | k1_xboole_0 = sK3
% 3.05/0.99      | k1_xboole_0 = sK5 ),
% 3.05/0.99      inference(unflattening,[status(thm)],[c_629]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1710,plain,
% 3.05/0.99      ( sK4 != k1_xboole_0
% 3.05/0.99      | k1_xboole_0 = sK3
% 3.05/0.99      | k1_xboole_0 = sK5
% 3.05/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1856,plain,
% 3.05/0.99      ( sK3 = k1_xboole_0
% 3.05/0.99      | sK4 != k1_xboole_0
% 3.05/0.99      | sK5 = k1_xboole_0
% 3.05/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_1710,c_9]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4274,plain,
% 3.05/0.99      ( sK3 = k1_xboole_0
% 3.05/0.99      | sK5 = k1_xboole_0
% 3.05/0.99      | k1_xboole_0 != k1_xboole_0
% 3.05/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4258,c_1856]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4325,plain,
% 3.05/0.99      ( sK3 = k1_xboole_0
% 3.05/0.99      | sK5 = k1_xboole_0
% 3.05/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.05/0.99      inference(equality_resolution_simp,[status(thm)],[c_4274]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4329,plain,
% 3.05/0.99      ( sK3 = k1_xboole_0 | sK5 = k1_xboole_0 ),
% 3.05/0.99      inference(forward_subsumption_resolution,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_4325,c_4287]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4261,plain,
% 3.05/0.99      ( k1_relat_1(sK5) != sK3
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4258,c_4243]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4376,plain,
% 3.05/0.99      ( k1_relat_1(sK5) != sK3
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4261,c_10]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4268,plain,
% 3.05/0.99      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK5)))) = iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4258,c_3262]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4345,plain,
% 3.05/0.99      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4268,c_10]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4790,plain,
% 3.05/0.99      ( k1_relat_1(sK5) != sK3 ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_4376,c_4345]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5119,plain,
% 3.05/0.99      ( sK3 != k1_xboole_0 | sK5 = k1_xboole_0 ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_5112,c_4790]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5147,plain,
% 3.05/0.99      ( sK5 = k1_xboole_0 ),
% 3.05/0.99      inference(global_propositional_subsumption,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_5140,c_4329,c_5119]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_891,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2212,plain,
% 3.05/0.99      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_891]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5088,plain,
% 3.05/0.99      ( k1_relat_1(k2_funct_1(sK5)) != X0
% 3.05/0.99      | sK4 != X0
% 3.05/0.99      | sK4 = k1_relat_1(k2_funct_1(sK5)) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_2212]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5092,plain,
% 3.05/0.99      ( k1_relat_1(k2_funct_1(sK5)) != k1_xboole_0
% 3.05/0.99      | sK4 = k1_relat_1(k2_funct_1(sK5))
% 3.05/0.99      | sK4 != k1_xboole_0 ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_5088]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_810,plain,
% 3.05/0.99      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.05/0.99      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.05/0.99      | k2_funct_1(sK5) != sK5
% 3.05/0.99      | sK3 != sK4 ),
% 3.05/0.99      inference(resolution_lifted,[status(thm)],[c_35,c_39]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1702,plain,
% 3.05/0.99      ( k2_funct_1(sK5) != sK5
% 3.05/0.99      | sK3 != sK4
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_810]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4279,plain,
% 3.05/0.99      ( k2_funct_1(sK5) != sK5
% 3.05/0.99      | sK3 != k1_xboole_0
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) != iProver_top
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4258,c_1702]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4300,plain,
% 3.05/0.99      ( k2_funct_1(sK5) != sK5
% 3.05/0.99      | sK3 != k1_xboole_0
% 3.05/0.99      | m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4279,c_10]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4348,plain,
% 3.05/0.99      ( k2_funct_1(sK5) != sK5
% 3.05/0.99      | sK3 != k1_xboole_0
% 3.05/0.99      | v1_funct_1(k2_funct_1(sK5)) != iProver_top ),
% 3.05/0.99      inference(backward_subsumption_resolution,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_4345,c_4300]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4384,plain,
% 3.05/0.99      ( ~ v1_funct_1(k2_funct_1(sK5))
% 3.05/0.99      | k2_funct_1(sK5) != sK5
% 3.05/0.99      | sK3 != k1_xboole_0 ),
% 3.05/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4348]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_13,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.05/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_1727,plain,
% 3.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.05/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.05/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3036,plain,
% 3.05/0.99      ( r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(k2_relat_1(sK5),k1_relat_1(sK5))) = iProver_top ),
% 3.05/0.99      inference(superposition,[status(thm)],[c_3031,c_1727]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3261,plain,
% 3.05/0.99      ( r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(sK4,k1_relat_1(sK5))) = iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_3232,c_3036]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4269,plain,
% 3.05/0.99      ( r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK5))) = iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4258,c_3261]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4342,plain,
% 3.05/0.99      ( r1_tarski(k2_funct_1(sK5),k1_xboole_0) = iProver_top ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4269,c_10]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4381,plain,
% 3.05/0.99      ( r1_tarski(k2_funct_1(sK5),k1_xboole_0) ),
% 3.05/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4342]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3264,plain,
% 3.05/0.99      ( k1_relat_1(k2_funct_1(sK5)) = sK4 ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_3232,c_2054]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4271,plain,
% 3.05/0.99      ( k1_relat_1(k2_funct_1(sK5)) = k1_xboole_0 ),
% 3.05/0.99      inference(demodulation,[status(thm)],[c_4258,c_3264]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4230,plain,
% 3.05/0.99      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.05/0.99      | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) = k1_relat_1(k2_funct_1(sK5)) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3055,plain,
% 3.05/0.99      ( k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != X0
% 3.05/0.99      | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) = sK4
% 3.05/0.99      | sK4 != X0 ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_891]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_4229,plain,
% 3.05/0.99      ( k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != k1_relat_1(k2_funct_1(sK5))
% 3.05/0.99      | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) = sK4
% 3.05/0.99      | sK4 != k1_relat_1(k2_funct_1(sK5)) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_3055]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2192,plain,
% 3.05/0.99      ( X0 != X1 | k2_funct_1(sK5) != X1 | k2_funct_1(sK5) = X0 ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_891]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3686,plain,
% 3.05/0.99      ( k2_funct_1(sK5) != X0 | k2_funct_1(sK5) = sK5 | sK5 != X0 ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_2192]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3690,plain,
% 3.05/0.99      ( k2_funct_1(sK5) = sK5
% 3.05/0.99      | k2_funct_1(sK5) != k1_xboole_0
% 3.05/0.99      | sK5 != k1_xboole_0 ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_3686]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_3,plain,
% 3.05/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2253,plain,
% 3.05/0.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.05/0.99      | r2_hidden(sK1(X0,k2_zfmisc_1(X1,X2)),X0) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2670,plain,
% 3.05/0.99      ( r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3))
% 3.05/0.99      | r2_hidden(sK1(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)),k2_funct_1(sK5)) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_2253]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_12,plain,
% 3.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.05/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2040,plain,
% 3.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.99      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2522,plain,
% 3.05/0.99      ( m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.05/0.99      | ~ r1_tarski(k2_funct_1(sK5),k2_zfmisc_1(sK4,sK3)) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_2040]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2412,plain,
% 3.05/0.99      ( r1_tarski(X0,k2_funct_1(sK5))
% 3.05/0.99      | r2_hidden(sK1(X0,k2_funct_1(sK5)),X0) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2424,plain,
% 3.05/0.99      ( r1_tarski(k1_xboole_0,k2_funct_1(sK5))
% 3.05/0.99      | r2_hidden(sK1(k1_xboole_0,k2_funct_1(sK5)),k1_xboole_0) ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_2412]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_890,plain,( X0 = X0 ),theory(equality) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2211,plain,
% 3.05/0.99      ( sK3 = sK3 ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_890]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2082,plain,
% 3.05/0.99      ( sK3 != X0 | sK3 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_891]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2210,plain,
% 3.05/0.99      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_2082]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_6,plain,
% 3.05/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.05/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2193,plain,
% 3.05/0.99      ( ~ r1_tarski(X0,k2_funct_1(sK5))
% 3.05/0.99      | ~ r1_tarski(k2_funct_1(sK5),X0)
% 3.05/0.99      | k2_funct_1(sK5) = X0 ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2195,plain,
% 3.05/0.99      ( ~ r1_tarski(k2_funct_1(sK5),k1_xboole_0)
% 3.05/0.99      | ~ r1_tarski(k1_xboole_0,k2_funct_1(sK5))
% 3.05/0.99      | k2_funct_1(sK5) = k1_xboole_0 ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_2193]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_892,plain,
% 3.05/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.05/0.99      theory(equality) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2169,plain,
% 3.05/0.99      ( ~ v1_xboole_0(X0)
% 3.05/0.99      | v1_xboole_0(k2_funct_1(sK5))
% 3.05/0.99      | k2_funct_1(sK5) != X0 ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_892]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_2171,plain,
% 3.05/0.99      ( v1_xboole_0(k2_funct_1(sK5))
% 3.05/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.05/0.99      | k2_funct_1(sK5) != k1_xboole_0 ),
% 3.05/0.99      inference(instantiation,[status(thm)],[c_2169]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_25,plain,
% 3.05/0.99      ( v1_funct_2(X0,X1,X2)
% 3.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.05/0.99      | k1_xboole_0 = X2 ),
% 3.05/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_751,plain,
% 3.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.99      | ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.05/0.99      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.05/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.05/0.99      | k2_funct_1(sK5) != X0
% 3.05/0.99      | sK3 != X2
% 3.05/0.99      | sK4 != X1
% 3.05/0.99      | k1_xboole_0 = X2 ),
% 3.05/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_35]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_752,plain,
% 3.05/0.99      ( ~ m1_subset_1(k2_funct_1(sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
% 3.05/0.99      | ~ v1_funct_1(k2_funct_1(sK5))
% 3.05/0.99      | k1_relset_1(sK4,sK3,k2_funct_1(sK5)) != sK4
% 3.05/0.99      | k1_xboole_0 = sK3 ),
% 3.05/0.99      inference(unflattening,[status(thm)],[c_751]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(c_5,plain,
% 3.05/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.05/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.05/0.99  
% 3.05/0.99  cnf(contradiction,plain,
% 3.05/0.99      ( $false ),
% 3.05/0.99      inference(minisat,
% 3.05/0.99                [status(thm)],
% 3.05/0.99                [c_5572,c_5215,c_5147,c_5092,c_4384,c_4381,c_4271,c_4258,
% 3.05/0.99                 c_4230,c_4229,c_3690,c_2670,c_2522,c_2424,c_2211,c_2210,
% 3.05/0.99                 c_2195,c_2171,c_2147,c_2045,c_752,c_5,c_38,c_40]) ).
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.05/0.99  
% 3.05/0.99  ------                               Statistics
% 3.05/0.99  
% 3.05/0.99  ------ General
% 3.05/0.99  
% 3.05/0.99  abstr_ref_over_cycles:                  0
% 3.05/0.99  abstr_ref_under_cycles:                 0
% 3.05/0.99  gc_basic_clause_elim:                   0
% 3.05/0.99  forced_gc_time:                         0
% 3.05/0.99  parsing_time:                           0.012
% 3.05/0.99  unif_index_cands_time:                  0.
% 3.05/0.99  unif_index_add_time:                    0.
% 3.05/0.99  orderings_time:                         0.
% 3.05/0.99  out_proof_time:                         0.014
% 3.05/0.99  total_time:                             0.181
% 3.05/0.99  num_of_symbols:                         53
% 3.05/0.99  num_of_terms:                           4549
% 3.05/0.99  
% 3.05/0.99  ------ Preprocessing
% 3.05/0.99  
% 3.05/0.99  num_of_splits:                          0
% 3.05/0.99  num_of_split_atoms:                     0
% 3.05/0.99  num_of_reused_defs:                     0
% 3.05/0.99  num_eq_ax_congr_red:                    16
% 3.05/0.99  num_of_sem_filtered_clauses:            1
% 3.05/0.99  num_of_subtypes:                        0
% 3.05/0.99  monotx_restored_types:                  0
% 3.05/0.99  sat_num_of_epr_types:                   0
% 3.05/0.99  sat_num_of_non_cyclic_types:            0
% 3.05/0.99  sat_guarded_non_collapsed_types:        0
% 3.05/0.99  num_pure_diseq_elim:                    0
% 3.05/0.99  simp_replaced_by:                       0
% 3.05/0.99  res_preprocessed:                       156
% 3.05/0.99  prep_upred:                             0
% 3.05/0.99  prep_unflattend:                        57
% 3.05/0.99  smt_new_axioms:                         0
% 3.05/0.99  pred_elim_cands:                        8
% 3.05/0.99  pred_elim:                              2
% 3.05/0.99  pred_elim_cl:                           -4
% 3.05/0.99  pred_elim_cycles:                       4
% 3.05/0.99  merged_defs:                            6
% 3.05/0.99  merged_defs_ncl:                        0
% 3.05/0.99  bin_hyper_res:                          6
% 3.05/0.99  prep_cycles:                            3
% 3.05/0.99  pred_elim_time:                         0.009
% 3.05/0.99  splitting_time:                         0.
% 3.05/0.99  sem_filter_time:                        0.
% 3.05/0.99  monotx_time:                            0.
% 3.05/0.99  subtype_inf_time:                       0.
% 3.05/0.99  
% 3.05/0.99  ------ Problem properties
% 3.05/0.99  
% 3.05/0.99  clauses:                                43
% 3.05/0.99  conjectures:                            3
% 3.05/0.99  epr:                                    7
% 3.05/0.99  horn:                                   34
% 3.05/0.99  ground:                                 15
% 3.05/0.99  unary:                                  11
% 3.05/0.99  binary:                                 15
% 3.05/0.99  lits:                                   105
% 3.05/0.99  lits_eq:                                42
% 3.05/0.99  fd_pure:                                0
% 3.05/0.99  fd_pseudo:                              0
% 3.05/0.99  fd_cond:                                3
% 3.05/0.99  fd_pseudo_cond:                         1
% 3.05/0.99  ac_symbols:                             0
% 3.05/0.99  
% 3.05/0.99  ------ Propositional Solver
% 3.05/0.99  
% 3.05/0.99  prop_solver_calls:                      24
% 3.05/0.99  prop_fast_solver_calls:                 1073
% 3.05/0.99  smt_solver_calls:                       0
% 3.05/0.99  smt_fast_solver_calls:                  0
% 3.05/0.99  prop_num_of_clauses:                    1782
% 3.05/0.99  prop_preprocess_simplified:             6141
% 3.05/0.99  prop_fo_subsumed:                       28
% 3.05/0.99  prop_solver_time:                       0.
% 3.05/0.99  smt_solver_time:                        0.
% 3.05/0.99  smt_fast_solver_time:                   0.
% 3.05/0.99  prop_fast_solver_time:                  0.
% 3.05/0.99  prop_unsat_core_time:                   0.
% 3.05/0.99  
% 3.05/0.99  ------ QBF
% 3.05/0.99  
% 3.05/0.99  qbf_q_res:                              0
% 3.05/0.99  qbf_num_tautologies:                    0
% 3.05/0.99  qbf_prep_cycles:                        0
% 3.05/0.99  
% 3.05/0.99  ------ BMC1
% 3.05/0.99  
% 3.05/0.99  bmc1_current_bound:                     -1
% 3.05/0.99  bmc1_last_solved_bound:                 -1
% 3.05/0.99  bmc1_unsat_core_size:                   -1
% 3.05/0.99  bmc1_unsat_core_parents_size:           -1
% 3.05/0.99  bmc1_merge_next_fun:                    0
% 3.05/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.05/0.99  
% 3.05/0.99  ------ Instantiation
% 3.05/0.99  
% 3.05/0.99  inst_num_of_clauses:                    572
% 3.05/0.99  inst_num_in_passive:                    180
% 3.05/0.99  inst_num_in_active:                     321
% 3.05/0.99  inst_num_in_unprocessed:                70
% 3.05/0.99  inst_num_of_loops:                      496
% 3.05/0.99  inst_num_of_learning_restarts:          0
% 3.05/0.99  inst_num_moves_active_passive:          171
% 3.05/0.99  inst_lit_activity:                      0
% 3.05/0.99  inst_lit_activity_moves:                0
% 3.05/0.99  inst_num_tautologies:                   0
% 3.05/0.99  inst_num_prop_implied:                  0
% 3.05/0.99  inst_num_existing_simplified:           0
% 3.05/0.99  inst_num_eq_res_simplified:             0
% 3.05/0.99  inst_num_child_elim:                    0
% 3.05/0.99  inst_num_of_dismatching_blockings:      182
% 3.05/0.99  inst_num_of_non_proper_insts:           511
% 3.05/0.99  inst_num_of_duplicates:                 0
% 3.05/0.99  inst_inst_num_from_inst_to_res:         0
% 3.05/0.99  inst_dismatching_checking_time:         0.
% 3.05/0.99  
% 3.05/0.99  ------ Resolution
% 3.05/0.99  
% 3.05/0.99  res_num_of_clauses:                     0
% 3.05/0.99  res_num_in_passive:                     0
% 3.05/0.99  res_num_in_active:                      0
% 3.05/0.99  res_num_of_loops:                       159
% 3.05/0.99  res_forward_subset_subsumed:            33
% 3.05/0.99  res_backward_subset_subsumed:           2
% 3.05/0.99  res_forward_subsumed:                   0
% 3.05/0.99  res_backward_subsumed:                  0
% 3.05/0.99  res_forward_subsumption_resolution:     5
% 3.05/0.99  res_backward_subsumption_resolution:    0
% 3.05/0.99  res_clause_to_clause_subsumption:       326
% 3.05/0.99  res_orphan_elimination:                 0
% 3.05/0.99  res_tautology_del:                      43
% 3.05/0.99  res_num_eq_res_simplified:              0
% 3.05/0.99  res_num_sel_changes:                    0
% 3.05/0.99  res_moves_from_active_to_pass:          0
% 3.05/0.99  
% 3.05/0.99  ------ Superposition
% 3.05/0.99  
% 3.05/0.99  sup_time_total:                         0.
% 3.05/0.99  sup_time_generating:                    0.
% 3.05/0.99  sup_time_sim_full:                      0.
% 3.05/0.99  sup_time_sim_immed:                     0.
% 3.05/0.99  
% 3.05/0.99  sup_num_of_clauses:                     122
% 3.05/0.99  sup_num_in_active:                      53
% 3.05/0.99  sup_num_in_passive:                     69
% 3.05/0.99  sup_num_of_loops:                       98
% 3.05/0.99  sup_fw_superposition:                   92
% 3.05/0.99  sup_bw_superposition:                   55
% 3.05/0.99  sup_immediate_simplified:               62
% 3.05/0.99  sup_given_eliminated:                   0
% 3.05/0.99  comparisons_done:                       0
% 3.05/0.99  comparisons_avoided:                    13
% 3.05/0.99  
% 3.05/0.99  ------ Simplifications
% 3.05/0.99  
% 3.05/0.99  
% 3.05/0.99  sim_fw_subset_subsumed:                 14
% 3.05/0.99  sim_bw_subset_subsumed:                 4
% 3.05/0.99  sim_fw_subsumed:                        12
% 3.05/0.99  sim_bw_subsumed:                        1
% 3.05/0.99  sim_fw_subsumption_res:                 2
% 3.05/0.99  sim_bw_subsumption_res:                 3
% 3.05/0.99  sim_tautology_del:                      4
% 3.05/0.99  sim_eq_tautology_del:                   8
% 3.05/0.99  sim_eq_res_simp:                        3
% 3.05/0.99  sim_fw_demodulated:                     24
% 3.05/0.99  sim_bw_demodulated:                     45
% 3.05/0.99  sim_light_normalised:                   25
% 3.05/0.99  sim_joinable_taut:                      0
% 3.05/0.99  sim_joinable_simp:                      0
% 3.05/0.99  sim_ac_normalised:                      0
% 3.05/0.99  sim_smt_subsumption:                    0
% 3.05/0.99  
%------------------------------------------------------------------------------
