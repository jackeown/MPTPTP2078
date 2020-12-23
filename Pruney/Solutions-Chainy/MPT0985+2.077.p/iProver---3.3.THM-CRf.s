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
% DateTime   : Thu Dec  3 12:02:35 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  203 (6252 expanded)
%              Number of clauses        :  132 (1931 expanded)
%              Number of leaves         :   21 (1226 expanded)
%              Depth                    :   29
%              Number of atoms          :  586 (32982 expanded)
%              Number of equality atoms :  260 (5809 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f62,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f41,plain,(
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

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f47,plain,
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

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f42,f47])).

fof(f84,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f48])).

fof(f61,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f60,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK0(X0,X1),X0,X1)
        & v1_funct_1(sK0(X0,X1))
        & v4_relat_1(sK0(X0,X1),X0)
        & v1_relat_1(sK0(X0,X1))
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK0(X0,X1),X0,X1)
      & v1_funct_1(sK0(X0,X1))
      & v4_relat_1(sK0(X0,X1),X0)
      & v1_relat_1(sK0(X0,X1))
      & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f45])).

fof(f67,plain,(
    ! [X0,X1] : m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    ! [X0,X1] : v1_funct_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X0,X1] : v1_funct_2(sK0(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_34,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_401,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_34])).

cnf(c_402,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_404,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_402,c_37])).

cnf(c_1614,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1892,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1933,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1614,c_37,c_35,c_402,c_1892])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1625,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4455,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1933,c_1625])).

cnf(c_1618,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1630,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3502,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1618,c_1630])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3504,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3502,c_33])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_387,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_34])).

cnf(c_388,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_390,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_37])).

cnf(c_1615,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_1996,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1615,c_37,c_35,c_388,c_1892])).

cnf(c_3633,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3504,c_1996])).

cnf(c_4509,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4455,c_3633])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1873,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1874,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1873])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1881,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1882,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1881])).

cnf(c_1893,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1892])).

cnf(c_5356,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4509,c_38,c_40,c_1874,c_1882,c_1893])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ r1_tarski(X2,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1620,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5366,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),sK2,X0) = iProver_top
    | v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5356,c_1620])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1624,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4375,plain,
    ( v1_funct_2(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1933,c_1624])).

cnf(c_4379,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4375,c_3633])).

cnf(c_7879,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),sK2,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5366,c_38,c_40,c_1874,c_1882,c_1893,c_4379])).

cnf(c_7880,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),sK2,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7879])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(X2,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1622,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5365,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5356,c_1622])).

cnf(c_8030,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5365,c_38,c_40,c_1874,c_1882,c_1893,c_4379])).

cnf(c_8031,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_8030])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1619,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1926,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1619,c_38,c_40,c_42,c_1874,c_1893])).

cnf(c_1927,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1926])).

cnf(c_8043,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8031,c_1927])).

cnf(c_15,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_421,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_4])).

cnf(c_425,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_421,c_15,c_14,c_4])).

cnf(c_426,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(renaming,[status(thm)],[c_425])).

cnf(c_1955,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_426])).

cnf(c_1956,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1955])).

cnf(c_8098,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8043,c_40,c_1956])).

cnf(c_8099,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_8098])).

cnf(c_8104,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7880,c_8099])).

cnf(c_8203,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8104,c_40,c_1956])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1636,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3483,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1933,c_1636])).

cnf(c_3487,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3483,c_1996])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2526,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4037,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3487,c_35,c_1892,c_2526])).

cnf(c_4038,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4037])).

cnf(c_4039,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4038,c_3504])).

cnf(c_8222,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8203,c_4039])).

cnf(c_8235,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8222])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1637,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8264,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8203,c_1637])).

cnf(c_2082,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1058,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2130,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1058])).

cnf(c_1059,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2274,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1059])).

cnf(c_3067,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2274])).

cnf(c_3068,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_3067])).

cnf(c_8304,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8264,c_35,c_40,c_1892,c_1956,c_2082,c_2130,c_3068,c_8104])).

cnf(c_8320,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),sK2,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8304,c_1927])).

cnf(c_9024,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8235,c_8320])).

cnf(c_8317,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = sK2 ),
    inference(demodulation,[status(thm)],[c_8304,c_3633])).

cnf(c_8811,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | sK2 != k1_xboole_0
    | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8317,c_1637])).

cnf(c_22,plain,
    ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_57,plain,
    ( m1_subset_1(sK0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( v1_funct_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_65,plain,
    ( v1_funct_1(sK0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_67,plain,
    ( v1_funct_1(sK0(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_87,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_89,plain,
    ( v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1884,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1886,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1884])).

cnf(c_2,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1885,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1888,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1885])).

cnf(c_1068,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1915,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK0(X1,X2))
    | X0 != sK0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1068])).

cnf(c_1916,plain,
    ( X0 != sK0(X1,X2)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1915])).

cnf(c_1918,plain,
    ( k1_xboole_0 != sK0(k1_xboole_0,k1_xboole_0)
    | v1_funct_1(sK0(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1916])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2346,plain,
    ( ~ v1_xboole_0(sK0(X0,X1))
    | k1_xboole_0 = sK0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2350,plain,
    ( ~ v1_xboole_0(sK0(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = sK0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2346])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3265,plain,
    ( ~ m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(sK0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3267,plain,
    ( ~ m1_subset_1(sK0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v1_xboole_0(sK0(k1_xboole_0,k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3265])).

cnf(c_9451,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8811,c_40,c_57,c_67,c_89,c_0,c_1886,c_1888,c_1918,c_1956,c_2350,c_3267,c_4039,c_8104])).

cnf(c_9457,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9024,c_9451])).

cnf(c_1640,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1642,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1626,plain,
    ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1631,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4412,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1626,c_1631])).

cnf(c_1641,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5194,plain,
    ( sK0(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4412,c_1641])).

cnf(c_5219,plain,
    ( sK0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1642,c_5194])).

cnf(c_18,plain,
    ( v1_funct_2(sK0(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1629,plain,
    ( v1_funct_2(sK0(X0,X1),X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6022,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5219,c_1629])).

cnf(c_9460,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9457,c_1640,c_6022])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.27/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.27/0.99  
% 3.27/0.99  ------  iProver source info
% 3.27/0.99  
% 3.27/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.27/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.27/0.99  git: non_committed_changes: false
% 3.27/0.99  git: last_make_outside_of_git: false
% 3.27/0.99  
% 3.27/0.99  ------ 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options
% 3.27/0.99  
% 3.27/0.99  --out_options                           all
% 3.27/0.99  --tptp_safe_out                         true
% 3.27/0.99  --problem_path                          ""
% 3.27/0.99  --include_path                          ""
% 3.27/0.99  --clausifier                            res/vclausify_rel
% 3.27/0.99  --clausifier_options                    --mode clausify
% 3.27/0.99  --stdin                                 false
% 3.27/0.99  --stats_out                             all
% 3.27/0.99  
% 3.27/0.99  ------ General Options
% 3.27/0.99  
% 3.27/0.99  --fof                                   false
% 3.27/0.99  --time_out_real                         305.
% 3.27/0.99  --time_out_virtual                      -1.
% 3.27/0.99  --symbol_type_check                     false
% 3.27/0.99  --clausify_out                          false
% 3.27/0.99  --sig_cnt_out                           false
% 3.27/0.99  --trig_cnt_out                          false
% 3.27/0.99  --trig_cnt_out_tolerance                1.
% 3.27/0.99  --trig_cnt_out_sk_spl                   false
% 3.27/0.99  --abstr_cl_out                          false
% 3.27/0.99  
% 3.27/0.99  ------ Global Options
% 3.27/0.99  
% 3.27/0.99  --schedule                              default
% 3.27/0.99  --add_important_lit                     false
% 3.27/0.99  --prop_solver_per_cl                    1000
% 3.27/0.99  --min_unsat_core                        false
% 3.27/0.99  --soft_assumptions                      false
% 3.27/0.99  --soft_lemma_size                       3
% 3.27/0.99  --prop_impl_unit_size                   0
% 3.27/0.99  --prop_impl_unit                        []
% 3.27/0.99  --share_sel_clauses                     true
% 3.27/0.99  --reset_solvers                         false
% 3.27/0.99  --bc_imp_inh                            [conj_cone]
% 3.27/0.99  --conj_cone_tolerance                   3.
% 3.27/0.99  --extra_neg_conj                        none
% 3.27/0.99  --large_theory_mode                     true
% 3.27/0.99  --prolific_symb_bound                   200
% 3.27/0.99  --lt_threshold                          2000
% 3.27/0.99  --clause_weak_htbl                      true
% 3.27/0.99  --gc_record_bc_elim                     false
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing Options
% 3.27/0.99  
% 3.27/0.99  --preprocessing_flag                    true
% 3.27/0.99  --time_out_prep_mult                    0.1
% 3.27/0.99  --splitting_mode                        input
% 3.27/0.99  --splitting_grd                         true
% 3.27/0.99  --splitting_cvd                         false
% 3.27/0.99  --splitting_cvd_svl                     false
% 3.27/0.99  --splitting_nvd                         32
% 3.27/0.99  --sub_typing                            true
% 3.27/0.99  --prep_gs_sim                           true
% 3.27/0.99  --prep_unflatten                        true
% 3.27/0.99  --prep_res_sim                          true
% 3.27/0.99  --prep_upred                            true
% 3.27/0.99  --prep_sem_filter                       exhaustive
% 3.27/0.99  --prep_sem_filter_out                   false
% 3.27/0.99  --pred_elim                             true
% 3.27/0.99  --res_sim_input                         true
% 3.27/0.99  --eq_ax_congr_red                       true
% 3.27/0.99  --pure_diseq_elim                       true
% 3.27/0.99  --brand_transform                       false
% 3.27/0.99  --non_eq_to_eq                          false
% 3.27/0.99  --prep_def_merge                        true
% 3.27/0.99  --prep_def_merge_prop_impl              false
% 3.27/0.99  --prep_def_merge_mbd                    true
% 3.27/0.99  --prep_def_merge_tr_red                 false
% 3.27/0.99  --prep_def_merge_tr_cl                  false
% 3.27/0.99  --smt_preprocessing                     true
% 3.27/0.99  --smt_ac_axioms                         fast
% 3.27/0.99  --preprocessed_out                      false
% 3.27/0.99  --preprocessed_stats                    false
% 3.27/0.99  
% 3.27/0.99  ------ Abstraction refinement Options
% 3.27/0.99  
% 3.27/0.99  --abstr_ref                             []
% 3.27/0.99  --abstr_ref_prep                        false
% 3.27/0.99  --abstr_ref_until_sat                   false
% 3.27/0.99  --abstr_ref_sig_restrict                funpre
% 3.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/0.99  --abstr_ref_under                       []
% 3.27/0.99  
% 3.27/0.99  ------ SAT Options
% 3.27/0.99  
% 3.27/0.99  --sat_mode                              false
% 3.27/0.99  --sat_fm_restart_options                ""
% 3.27/0.99  --sat_gr_def                            false
% 3.27/0.99  --sat_epr_types                         true
% 3.27/0.99  --sat_non_cyclic_types                  false
% 3.27/0.99  --sat_finite_models                     false
% 3.27/0.99  --sat_fm_lemmas                         false
% 3.27/0.99  --sat_fm_prep                           false
% 3.27/0.99  --sat_fm_uc_incr                        true
% 3.27/0.99  --sat_out_model                         small
% 3.27/0.99  --sat_out_clauses                       false
% 3.27/0.99  
% 3.27/0.99  ------ QBF Options
% 3.27/0.99  
% 3.27/0.99  --qbf_mode                              false
% 3.27/0.99  --qbf_elim_univ                         false
% 3.27/0.99  --qbf_dom_inst                          none
% 3.27/0.99  --qbf_dom_pre_inst                      false
% 3.27/0.99  --qbf_sk_in                             false
% 3.27/0.99  --qbf_pred_elim                         true
% 3.27/0.99  --qbf_split                             512
% 3.27/0.99  
% 3.27/0.99  ------ BMC1 Options
% 3.27/0.99  
% 3.27/0.99  --bmc1_incremental                      false
% 3.27/0.99  --bmc1_axioms                           reachable_all
% 3.27/0.99  --bmc1_min_bound                        0
% 3.27/0.99  --bmc1_max_bound                        -1
% 3.27/0.99  --bmc1_max_bound_default                -1
% 3.27/0.99  --bmc1_symbol_reachability              true
% 3.27/0.99  --bmc1_property_lemmas                  false
% 3.27/0.99  --bmc1_k_induction                      false
% 3.27/0.99  --bmc1_non_equiv_states                 false
% 3.27/0.99  --bmc1_deadlock                         false
% 3.27/0.99  --bmc1_ucm                              false
% 3.27/0.99  --bmc1_add_unsat_core                   none
% 3.27/0.99  --bmc1_unsat_core_children              false
% 3.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/0.99  --bmc1_out_stat                         full
% 3.27/0.99  --bmc1_ground_init                      false
% 3.27/0.99  --bmc1_pre_inst_next_state              false
% 3.27/0.99  --bmc1_pre_inst_state                   false
% 3.27/0.99  --bmc1_pre_inst_reach_state             false
% 3.27/0.99  --bmc1_out_unsat_core                   false
% 3.27/0.99  --bmc1_aig_witness_out                  false
% 3.27/0.99  --bmc1_verbose                          false
% 3.27/0.99  --bmc1_dump_clauses_tptp                false
% 3.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.27/0.99  --bmc1_dump_file                        -
% 3.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.27/0.99  --bmc1_ucm_extend_mode                  1
% 3.27/0.99  --bmc1_ucm_init_mode                    2
% 3.27/0.99  --bmc1_ucm_cone_mode                    none
% 3.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.27/0.99  --bmc1_ucm_relax_model                  4
% 3.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/0.99  --bmc1_ucm_layered_model                none
% 3.27/0.99  --bmc1_ucm_max_lemma_size               10
% 3.27/0.99  
% 3.27/0.99  ------ AIG Options
% 3.27/0.99  
% 3.27/0.99  --aig_mode                              false
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation Options
% 3.27/0.99  
% 3.27/0.99  --instantiation_flag                    true
% 3.27/0.99  --inst_sos_flag                         false
% 3.27/0.99  --inst_sos_phase                        true
% 3.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel_side                     num_symb
% 3.27/0.99  --inst_solver_per_active                1400
% 3.27/0.99  --inst_solver_calls_frac                1.
% 3.27/0.99  --inst_passive_queue_type               priority_queues
% 3.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/0.99  --inst_passive_queues_freq              [25;2]
% 3.27/0.99  --inst_dismatching                      true
% 3.27/0.99  --inst_eager_unprocessed_to_passive     true
% 3.27/0.99  --inst_prop_sim_given                   true
% 3.27/0.99  --inst_prop_sim_new                     false
% 3.27/0.99  --inst_subs_new                         false
% 3.27/0.99  --inst_eq_res_simp                      false
% 3.27/0.99  --inst_subs_given                       false
% 3.27/0.99  --inst_orphan_elimination               true
% 3.27/0.99  --inst_learning_loop_flag               true
% 3.27/0.99  --inst_learning_start                   3000
% 3.27/0.99  --inst_learning_factor                  2
% 3.27/0.99  --inst_start_prop_sim_after_learn       3
% 3.27/0.99  --inst_sel_renew                        solver
% 3.27/0.99  --inst_lit_activity_flag                true
% 3.27/0.99  --inst_restr_to_given                   false
% 3.27/0.99  --inst_activity_threshold               500
% 3.27/0.99  --inst_out_proof                        true
% 3.27/0.99  
% 3.27/0.99  ------ Resolution Options
% 3.27/0.99  
% 3.27/0.99  --resolution_flag                       true
% 3.27/0.99  --res_lit_sel                           adaptive
% 3.27/0.99  --res_lit_sel_side                      none
% 3.27/0.99  --res_ordering                          kbo
% 3.27/0.99  --res_to_prop_solver                    active
% 3.27/0.99  --res_prop_simpl_new                    false
% 3.27/0.99  --res_prop_simpl_given                  true
% 3.27/0.99  --res_passive_queue_type                priority_queues
% 3.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/0.99  --res_passive_queues_freq               [15;5]
% 3.27/0.99  --res_forward_subs                      full
% 3.27/0.99  --res_backward_subs                     full
% 3.27/0.99  --res_forward_subs_resolution           true
% 3.27/0.99  --res_backward_subs_resolution          true
% 3.27/0.99  --res_orphan_elimination                true
% 3.27/0.99  --res_time_limit                        2.
% 3.27/0.99  --res_out_proof                         true
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Options
% 3.27/0.99  
% 3.27/0.99  --superposition_flag                    true
% 3.27/0.99  --sup_passive_queue_type                priority_queues
% 3.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.27/0.99  --demod_completeness_check              fast
% 3.27/0.99  --demod_use_ground                      true
% 3.27/0.99  --sup_to_prop_solver                    passive
% 3.27/0.99  --sup_prop_simpl_new                    true
% 3.27/0.99  --sup_prop_simpl_given                  true
% 3.27/0.99  --sup_fun_splitting                     false
% 3.27/0.99  --sup_smt_interval                      50000
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Simplification Setup
% 3.27/0.99  
% 3.27/0.99  --sup_indices_passive                   []
% 3.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_full_bw                           [BwDemod]
% 3.27/0.99  --sup_immed_triv                        [TrivRules]
% 3.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_immed_bw_main                     []
% 3.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  
% 3.27/0.99  ------ Combination Options
% 3.27/0.99  
% 3.27/0.99  --comb_res_mult                         3
% 3.27/0.99  --comb_sup_mult                         2
% 3.27/0.99  --comb_inst_mult                        10
% 3.27/0.99  
% 3.27/0.99  ------ Debug Options
% 3.27/0.99  
% 3.27/0.99  --dbg_backtrace                         false
% 3.27/0.99  --dbg_dump_prop_clauses                 false
% 3.27/0.99  --dbg_dump_prop_clauses_file            -
% 3.27/0.99  --dbg_out_stat                          false
% 3.27/0.99  ------ Parsing...
% 3.27/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.27/0.99  ------ Proving...
% 3.27/0.99  ------ Problem Properties 
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  clauses                                 32
% 3.27/0.99  conjectures                             5
% 3.27/0.99  EPR                                     4
% 3.27/0.99  Horn                                    30
% 3.27/0.99  unary                                   11
% 3.27/0.99  binary                                  7
% 3.27/0.99  lits                                    77
% 3.27/0.99  lits eq                                 15
% 3.27/0.99  fd_pure                                 0
% 3.27/0.99  fd_pseudo                               0
% 3.27/0.99  fd_cond                                 5
% 3.27/0.99  fd_pseudo_cond                          0
% 3.27/0.99  AC symbols                              0
% 3.27/0.99  
% 3.27/0.99  ------ Schedule dynamic 5 is on 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  ------ 
% 3.27/0.99  Current options:
% 3.27/0.99  ------ 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options
% 3.27/0.99  
% 3.27/0.99  --out_options                           all
% 3.27/0.99  --tptp_safe_out                         true
% 3.27/0.99  --problem_path                          ""
% 3.27/0.99  --include_path                          ""
% 3.27/0.99  --clausifier                            res/vclausify_rel
% 3.27/0.99  --clausifier_options                    --mode clausify
% 3.27/0.99  --stdin                                 false
% 3.27/0.99  --stats_out                             all
% 3.27/0.99  
% 3.27/0.99  ------ General Options
% 3.27/0.99  
% 3.27/0.99  --fof                                   false
% 3.27/0.99  --time_out_real                         305.
% 3.27/0.99  --time_out_virtual                      -1.
% 3.27/0.99  --symbol_type_check                     false
% 3.27/0.99  --clausify_out                          false
% 3.27/0.99  --sig_cnt_out                           false
% 3.27/0.99  --trig_cnt_out                          false
% 3.27/0.99  --trig_cnt_out_tolerance                1.
% 3.27/0.99  --trig_cnt_out_sk_spl                   false
% 3.27/0.99  --abstr_cl_out                          false
% 3.27/0.99  
% 3.27/0.99  ------ Global Options
% 3.27/0.99  
% 3.27/0.99  --schedule                              default
% 3.27/0.99  --add_important_lit                     false
% 3.27/0.99  --prop_solver_per_cl                    1000
% 3.27/0.99  --min_unsat_core                        false
% 3.27/0.99  --soft_assumptions                      false
% 3.27/0.99  --soft_lemma_size                       3
% 3.27/0.99  --prop_impl_unit_size                   0
% 3.27/0.99  --prop_impl_unit                        []
% 3.27/0.99  --share_sel_clauses                     true
% 3.27/0.99  --reset_solvers                         false
% 3.27/0.99  --bc_imp_inh                            [conj_cone]
% 3.27/0.99  --conj_cone_tolerance                   3.
% 3.27/0.99  --extra_neg_conj                        none
% 3.27/0.99  --large_theory_mode                     true
% 3.27/0.99  --prolific_symb_bound                   200
% 3.27/0.99  --lt_threshold                          2000
% 3.27/0.99  --clause_weak_htbl                      true
% 3.27/0.99  --gc_record_bc_elim                     false
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing Options
% 3.27/0.99  
% 3.27/0.99  --preprocessing_flag                    true
% 3.27/0.99  --time_out_prep_mult                    0.1
% 3.27/0.99  --splitting_mode                        input
% 3.27/0.99  --splitting_grd                         true
% 3.27/0.99  --splitting_cvd                         false
% 3.27/0.99  --splitting_cvd_svl                     false
% 3.27/0.99  --splitting_nvd                         32
% 3.27/0.99  --sub_typing                            true
% 3.27/0.99  --prep_gs_sim                           true
% 3.27/0.99  --prep_unflatten                        true
% 3.27/0.99  --prep_res_sim                          true
% 3.27/0.99  --prep_upred                            true
% 3.27/0.99  --prep_sem_filter                       exhaustive
% 3.27/0.99  --prep_sem_filter_out                   false
% 3.27/0.99  --pred_elim                             true
% 3.27/0.99  --res_sim_input                         true
% 3.27/0.99  --eq_ax_congr_red                       true
% 3.27/0.99  --pure_diseq_elim                       true
% 3.27/0.99  --brand_transform                       false
% 3.27/0.99  --non_eq_to_eq                          false
% 3.27/0.99  --prep_def_merge                        true
% 3.27/0.99  --prep_def_merge_prop_impl              false
% 3.27/0.99  --prep_def_merge_mbd                    true
% 3.27/0.99  --prep_def_merge_tr_red                 false
% 3.27/0.99  --prep_def_merge_tr_cl                  false
% 3.27/0.99  --smt_preprocessing                     true
% 3.27/0.99  --smt_ac_axioms                         fast
% 3.27/0.99  --preprocessed_out                      false
% 3.27/0.99  --preprocessed_stats                    false
% 3.27/0.99  
% 3.27/0.99  ------ Abstraction refinement Options
% 3.27/0.99  
% 3.27/0.99  --abstr_ref                             []
% 3.27/0.99  --abstr_ref_prep                        false
% 3.27/0.99  --abstr_ref_until_sat                   false
% 3.27/0.99  --abstr_ref_sig_restrict                funpre
% 3.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/0.99  --abstr_ref_under                       []
% 3.27/0.99  
% 3.27/0.99  ------ SAT Options
% 3.27/0.99  
% 3.27/0.99  --sat_mode                              false
% 3.27/0.99  --sat_fm_restart_options                ""
% 3.27/0.99  --sat_gr_def                            false
% 3.27/0.99  --sat_epr_types                         true
% 3.27/0.99  --sat_non_cyclic_types                  false
% 3.27/0.99  --sat_finite_models                     false
% 3.27/0.99  --sat_fm_lemmas                         false
% 3.27/0.99  --sat_fm_prep                           false
% 3.27/0.99  --sat_fm_uc_incr                        true
% 3.27/0.99  --sat_out_model                         small
% 3.27/0.99  --sat_out_clauses                       false
% 3.27/0.99  
% 3.27/0.99  ------ QBF Options
% 3.27/0.99  
% 3.27/0.99  --qbf_mode                              false
% 3.27/0.99  --qbf_elim_univ                         false
% 3.27/0.99  --qbf_dom_inst                          none
% 3.27/0.99  --qbf_dom_pre_inst                      false
% 3.27/0.99  --qbf_sk_in                             false
% 3.27/0.99  --qbf_pred_elim                         true
% 3.27/0.99  --qbf_split                             512
% 3.27/0.99  
% 3.27/0.99  ------ BMC1 Options
% 3.27/0.99  
% 3.27/0.99  --bmc1_incremental                      false
% 3.27/0.99  --bmc1_axioms                           reachable_all
% 3.27/0.99  --bmc1_min_bound                        0
% 3.27/0.99  --bmc1_max_bound                        -1
% 3.27/0.99  --bmc1_max_bound_default                -1
% 3.27/0.99  --bmc1_symbol_reachability              true
% 3.27/0.99  --bmc1_property_lemmas                  false
% 3.27/0.99  --bmc1_k_induction                      false
% 3.27/0.99  --bmc1_non_equiv_states                 false
% 3.27/0.99  --bmc1_deadlock                         false
% 3.27/0.99  --bmc1_ucm                              false
% 3.27/0.99  --bmc1_add_unsat_core                   none
% 3.27/0.99  --bmc1_unsat_core_children              false
% 3.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/0.99  --bmc1_out_stat                         full
% 3.27/0.99  --bmc1_ground_init                      false
% 3.27/0.99  --bmc1_pre_inst_next_state              false
% 3.27/0.99  --bmc1_pre_inst_state                   false
% 3.27/0.99  --bmc1_pre_inst_reach_state             false
% 3.27/0.99  --bmc1_out_unsat_core                   false
% 3.27/0.99  --bmc1_aig_witness_out                  false
% 3.27/0.99  --bmc1_verbose                          false
% 3.27/0.99  --bmc1_dump_clauses_tptp                false
% 3.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.27/0.99  --bmc1_dump_file                        -
% 3.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.27/0.99  --bmc1_ucm_extend_mode                  1
% 3.27/0.99  --bmc1_ucm_init_mode                    2
% 3.27/0.99  --bmc1_ucm_cone_mode                    none
% 3.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.27/0.99  --bmc1_ucm_relax_model                  4
% 3.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/0.99  --bmc1_ucm_layered_model                none
% 3.27/0.99  --bmc1_ucm_max_lemma_size               10
% 3.27/0.99  
% 3.27/0.99  ------ AIG Options
% 3.27/0.99  
% 3.27/0.99  --aig_mode                              false
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation Options
% 3.27/0.99  
% 3.27/0.99  --instantiation_flag                    true
% 3.27/0.99  --inst_sos_flag                         false
% 3.27/0.99  --inst_sos_phase                        true
% 3.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel_side                     none
% 3.27/0.99  --inst_solver_per_active                1400
% 3.27/0.99  --inst_solver_calls_frac                1.
% 3.27/0.99  --inst_passive_queue_type               priority_queues
% 3.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/0.99  --inst_passive_queues_freq              [25;2]
% 3.27/0.99  --inst_dismatching                      true
% 3.27/0.99  --inst_eager_unprocessed_to_passive     true
% 3.27/0.99  --inst_prop_sim_given                   true
% 3.27/0.99  --inst_prop_sim_new                     false
% 3.27/0.99  --inst_subs_new                         false
% 3.27/0.99  --inst_eq_res_simp                      false
% 3.27/0.99  --inst_subs_given                       false
% 3.27/0.99  --inst_orphan_elimination               true
% 3.27/0.99  --inst_learning_loop_flag               true
% 3.27/0.99  --inst_learning_start                   3000
% 3.27/0.99  --inst_learning_factor                  2
% 3.27/0.99  --inst_start_prop_sim_after_learn       3
% 3.27/0.99  --inst_sel_renew                        solver
% 3.27/0.99  --inst_lit_activity_flag                true
% 3.27/0.99  --inst_restr_to_given                   false
% 3.27/0.99  --inst_activity_threshold               500
% 3.27/0.99  --inst_out_proof                        true
% 3.27/0.99  
% 3.27/0.99  ------ Resolution Options
% 3.27/0.99  
% 3.27/0.99  --resolution_flag                       false
% 3.27/0.99  --res_lit_sel                           adaptive
% 3.27/0.99  --res_lit_sel_side                      none
% 3.27/0.99  --res_ordering                          kbo
% 3.27/0.99  --res_to_prop_solver                    active
% 3.27/0.99  --res_prop_simpl_new                    false
% 3.27/0.99  --res_prop_simpl_given                  true
% 3.27/0.99  --res_passive_queue_type                priority_queues
% 3.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/0.99  --res_passive_queues_freq               [15;5]
% 3.27/0.99  --res_forward_subs                      full
% 3.27/0.99  --res_backward_subs                     full
% 3.27/0.99  --res_forward_subs_resolution           true
% 3.27/0.99  --res_backward_subs_resolution          true
% 3.27/0.99  --res_orphan_elimination                true
% 3.27/0.99  --res_time_limit                        2.
% 3.27/0.99  --res_out_proof                         true
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Options
% 3.27/0.99  
% 3.27/0.99  --superposition_flag                    true
% 3.27/0.99  --sup_passive_queue_type                priority_queues
% 3.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.27/0.99  --demod_completeness_check              fast
% 3.27/0.99  --demod_use_ground                      true
% 3.27/0.99  --sup_to_prop_solver                    passive
% 3.27/0.99  --sup_prop_simpl_new                    true
% 3.27/0.99  --sup_prop_simpl_given                  true
% 3.27/0.99  --sup_fun_splitting                     false
% 3.27/0.99  --sup_smt_interval                      50000
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Simplification Setup
% 3.27/0.99  
% 3.27/0.99  --sup_indices_passive                   []
% 3.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_full_bw                           [BwDemod]
% 3.27/0.99  --sup_immed_triv                        [TrivRules]
% 3.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_immed_bw_main                     []
% 3.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  
% 3.27/0.99  ------ Combination Options
% 3.27/0.99  
% 3.27/0.99  --comb_res_mult                         3
% 3.27/0.99  --comb_sup_mult                         2
% 3.27/0.99  --comb_inst_mult                        10
% 3.27/0.99  
% 3.27/0.99  ------ Debug Options
% 3.27/0.99  
% 3.27/0.99  --dbg_backtrace                         false
% 3.27/0.99  --dbg_dump_prop_clauses                 false
% 3.27/0.99  --dbg_dump_prop_clauses_file            -
% 3.27/0.99  --dbg_out_stat                          false
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  ------ Proving...
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  % SZS status Theorem for theBenchmark.p
% 3.27/0.99  
% 3.27/0.99   Resolution empty clause
% 3.27/0.99  
% 3.27/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  fof(f10,axiom,(
% 3.27/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f31,plain,(
% 3.27/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.27/0.99    inference(ennf_transformation,[],[f10])).
% 3.27/0.99  
% 3.27/0.99  fof(f32,plain,(
% 3.27/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.27/0.99    inference(flattening,[],[f31])).
% 3.27/0.99  
% 3.27/0.99  fof(f62,plain,(
% 3.27/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f32])).
% 3.27/0.99  
% 3.27/0.99  fof(f18,conjecture,(
% 3.27/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f19,negated_conjecture,(
% 3.27/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.27/0.99    inference(negated_conjecture,[],[f18])).
% 3.27/0.99  
% 3.27/0.99  fof(f41,plain,(
% 3.27/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.27/0.99    inference(ennf_transformation,[],[f19])).
% 3.27/0.99  
% 3.27/0.99  fof(f42,plain,(
% 3.27/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.27/0.99    inference(flattening,[],[f41])).
% 3.27/0.99  
% 3.27/0.99  fof(f47,plain,(
% 3.27/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f48,plain,(
% 3.27/0.99    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f42,f47])).
% 3.27/0.99  
% 3.27/0.99  fof(f84,plain,(
% 3.27/0.99    v2_funct_1(sK3)),
% 3.27/0.99    inference(cnf_transformation,[],[f48])).
% 3.27/0.99  
% 3.27/0.99  fof(f81,plain,(
% 3.27/0.99    v1_funct_1(sK3)),
% 3.27/0.99    inference(cnf_transformation,[],[f48])).
% 3.27/0.99  
% 3.27/0.99  fof(f83,plain,(
% 3.27/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.27/0.99    inference(cnf_transformation,[],[f48])).
% 3.27/0.99  
% 3.27/0.99  fof(f11,axiom,(
% 3.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f33,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/0.99    inference(ennf_transformation,[],[f11])).
% 3.27/0.99  
% 3.27/0.99  fof(f63,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f33])).
% 3.27/0.99  
% 3.27/0.99  fof(f16,axiom,(
% 3.27/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f37,plain,(
% 3.27/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.27/0.99    inference(ennf_transformation,[],[f16])).
% 3.27/0.99  
% 3.27/0.99  fof(f38,plain,(
% 3.27/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.27/0.99    inference(flattening,[],[f37])).
% 3.27/0.99  
% 3.27/0.99  fof(f74,plain,(
% 3.27/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f38])).
% 3.27/0.99  
% 3.27/0.99  fof(f14,axiom,(
% 3.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f36,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/0.99    inference(ennf_transformation,[],[f14])).
% 3.27/0.99  
% 3.27/0.99  fof(f66,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f36])).
% 3.27/0.99  
% 3.27/0.99  fof(f85,plain,(
% 3.27/0.99    k2_relset_1(sK1,sK2,sK3) = sK2),
% 3.27/0.99    inference(cnf_transformation,[],[f48])).
% 3.27/0.99  
% 3.27/0.99  fof(f61,plain,(
% 3.27/0.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f32])).
% 3.27/0.99  
% 3.27/0.99  fof(f9,axiom,(
% 3.27/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f29,plain,(
% 3.27/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.27/0.99    inference(ennf_transformation,[],[f9])).
% 3.27/0.99  
% 3.27/0.99  fof(f30,plain,(
% 3.27/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.27/0.99    inference(flattening,[],[f29])).
% 3.27/0.99  
% 3.27/0.99  fof(f60,plain,(
% 3.27/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f30])).
% 3.27/0.99  
% 3.27/0.99  fof(f59,plain,(
% 3.27/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f30])).
% 3.27/0.99  
% 3.27/0.99  fof(f17,axiom,(
% 3.27/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f39,plain,(
% 3.27/0.99    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.27/0.99    inference(ennf_transformation,[],[f17])).
% 3.27/0.99  
% 3.27/0.99  fof(f40,plain,(
% 3.27/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.27/0.99    inference(flattening,[],[f39])).
% 3.27/0.99  
% 3.27/0.99  fof(f77,plain,(
% 3.27/0.99    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f40])).
% 3.27/0.99  
% 3.27/0.99  fof(f73,plain,(
% 3.27/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f38])).
% 3.27/0.99  
% 3.27/0.99  fof(f79,plain,(
% 3.27/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f40])).
% 3.27/0.99  
% 3.27/0.99  fof(f86,plain,(
% 3.27/0.99    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 3.27/0.99    inference(cnf_transformation,[],[f48])).
% 3.27/0.99  
% 3.27/0.99  fof(f12,axiom,(
% 3.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f20,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.27/0.99    inference(pure_predicate_removal,[],[f12])).
% 3.27/0.99  
% 3.27/0.99  fof(f34,plain,(
% 3.27/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/0.99    inference(ennf_transformation,[],[f20])).
% 3.27/0.99  
% 3.27/0.99  fof(f64,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f34])).
% 3.27/0.99  
% 3.27/0.99  fof(f5,axiom,(
% 3.27/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f24,plain,(
% 3.27/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.27/0.99    inference(ennf_transformation,[],[f5])).
% 3.27/0.99  
% 3.27/0.99  fof(f43,plain,(
% 3.27/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.27/0.99    inference(nnf_transformation,[],[f24])).
% 3.27/0.99  
% 3.27/0.99  fof(f52,plain,(
% 3.27/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f43])).
% 3.27/0.99  
% 3.27/0.99  fof(f8,axiom,(
% 3.27/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f28,plain,(
% 3.27/0.99    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.27/0.99    inference(ennf_transformation,[],[f8])).
% 3.27/0.99  
% 3.27/0.99  fof(f44,plain,(
% 3.27/0.99    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.27/0.99    inference(nnf_transformation,[],[f28])).
% 3.27/0.99  
% 3.27/0.99  fof(f58,plain,(
% 3.27/0.99    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f44])).
% 3.27/0.99  
% 3.27/0.99  fof(f57,plain,(
% 3.27/0.99    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f44])).
% 3.27/0.99  
% 3.27/0.99  fof(f7,axiom,(
% 3.27/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f26,plain,(
% 3.27/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.27/0.99    inference(ennf_transformation,[],[f7])).
% 3.27/0.99  
% 3.27/0.99  fof(f27,plain,(
% 3.27/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.27/0.99    inference(flattening,[],[f26])).
% 3.27/0.99  
% 3.27/0.99  fof(f55,plain,(
% 3.27/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f27])).
% 3.27/0.99  
% 3.27/0.99  fof(f15,axiom,(
% 3.27/0.99    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f21,plain,(
% 3.27/0.99    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/0.99    inference(pure_predicate_removal,[],[f15])).
% 3.27/0.99  
% 3.27/0.99  fof(f45,plain,(
% 3.27/0.99    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK0(X0,X1),X0,X1) & v1_funct_1(sK0(X0,X1)) & v4_relat_1(sK0(X0,X1),X0) & v1_relat_1(sK0(X0,X1)) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.27/0.99    introduced(choice_axiom,[])).
% 3.27/0.99  
% 3.27/0.99  fof(f46,plain,(
% 3.27/0.99    ! [X0,X1] : (v1_funct_2(sK0(X0,X1),X0,X1) & v1_funct_1(sK0(X0,X1)) & v4_relat_1(sK0(X0,X1),X0) & v1_relat_1(sK0(X0,X1)) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f45])).
% 3.27/0.99  
% 3.27/0.99  fof(f67,plain,(
% 3.27/0.99    ( ! [X0,X1] : (m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f46])).
% 3.27/0.99  
% 3.27/0.99  fof(f70,plain,(
% 3.27/0.99    ( ! [X0,X1] : (v1_funct_1(sK0(X0,X1))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f46])).
% 3.27/0.99  
% 3.27/0.99  fof(f1,axiom,(
% 3.27/0.99    v1_xboole_0(k1_xboole_0)),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f49,plain,(
% 3.27/0.99    v1_xboole_0(k1_xboole_0)),
% 3.27/0.99    inference(cnf_transformation,[],[f1])).
% 3.27/0.99  
% 3.27/0.99  fof(f3,axiom,(
% 3.27/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f51,plain,(
% 3.27/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.27/0.99    inference(cnf_transformation,[],[f3])).
% 3.27/0.99  
% 3.27/0.99  fof(f2,axiom,(
% 3.27/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f23,plain,(
% 3.27/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.27/0.99    inference(ennf_transformation,[],[f2])).
% 3.27/0.99  
% 3.27/0.99  fof(f50,plain,(
% 3.27/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f23])).
% 3.27/0.99  
% 3.27/0.99  fof(f13,axiom,(
% 3.27/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.27/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/0.99  
% 3.27/0.99  fof(f35,plain,(
% 3.27/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.27/0.99    inference(ennf_transformation,[],[f13])).
% 3.27/0.99  
% 3.27/0.99  fof(f65,plain,(
% 3.27/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f35])).
% 3.27/0.99  
% 3.27/0.99  fof(f71,plain,(
% 3.27/0.99    ( ! [X0,X1] : (v1_funct_2(sK0(X0,X1),X0,X1)) )),
% 3.27/0.99    inference(cnf_transformation,[],[f46])).
% 3.27/0.99  
% 3.27/0.99  cnf(c_12,plain,
% 3.27/0.99      ( ~ v2_funct_1(X0)
% 3.27/0.99      | ~ v1_funct_1(X0)
% 3.27/0.99      | ~ v1_relat_1(X0)
% 3.27/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_34,negated_conjecture,
% 3.27/0.99      ( v2_funct_1(sK3) ),
% 3.27/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_401,plain,
% 3.27/0.99      ( ~ v1_funct_1(X0)
% 3.27/0.99      | ~ v1_relat_1(X0)
% 3.27/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.27/0.99      | sK3 != X0 ),
% 3.27/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_34]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_402,plain,
% 3.27/0.99      ( ~ v1_funct_1(sK3)
% 3.27/0.99      | ~ v1_relat_1(sK3)
% 3.27/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.27/0.99      inference(unflattening,[status(thm)],[c_401]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_37,negated_conjecture,
% 3.27/0.99      ( v1_funct_1(sK3) ),
% 3.27/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_404,plain,
% 3.27/0.99      ( ~ v1_relat_1(sK3) | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.27/0.99      inference(global_propositional_subsumption,[status(thm)],[c_402,c_37]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1614,plain,
% 3.27/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.27/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_35,negated_conjecture,
% 3.27/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.27/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_14,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1892,plain,
% 3.27/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.27/0.99      | v1_relat_1(sK3) ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1933,plain,
% 3.27/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_1614,c_37,c_35,c_402,c_1892]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_23,plain,
% 3.27/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.27/0.99      | ~ v1_funct_1(X0)
% 3.27/0.99      | ~ v1_relat_1(X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1625,plain,
% 3.27/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.27/0.99      | v1_funct_1(X0) != iProver_top
% 3.27/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_4455,plain,
% 3.27/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 3.27/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.27/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1933,c_1625]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1618,plain,
% 3.27/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_17,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1630,plain,
% 3.27/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.27/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3502,plain,
% 3.27/0.99      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1618,c_1630]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_33,negated_conjecture,
% 3.27/0.99      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 3.27/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3504,plain,
% 3.27/0.99      ( k2_relat_1(sK3) = sK2 ),
% 3.27/0.99      inference(light_normalisation,[status(thm)],[c_3502,c_33]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_13,plain,
% 3.27/0.99      ( ~ v2_funct_1(X0)
% 3.27/0.99      | ~ v1_funct_1(X0)
% 3.27/0.99      | ~ v1_relat_1(X0)
% 3.27/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_387,plain,
% 3.27/0.99      ( ~ v1_funct_1(X0)
% 3.27/0.99      | ~ v1_relat_1(X0)
% 3.27/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.27/0.99      | sK3 != X0 ),
% 3.27/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_34]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_388,plain,
% 3.27/0.99      ( ~ v1_funct_1(sK3)
% 3.27/0.99      | ~ v1_relat_1(sK3)
% 3.27/0.99      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.27/0.99      inference(unflattening,[status(thm)],[c_387]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_390,plain,
% 3.27/0.99      ( ~ v1_relat_1(sK3) | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.27/0.99      inference(global_propositional_subsumption,[status(thm)],[c_388,c_37]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1615,plain,
% 3.27/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 3.27/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1996,plain,
% 3.27/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_1615,c_37,c_35,c_388,c_1892]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3633,plain,
% 3.27/0.99      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_3504,c_1996]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_4509,plain,
% 3.27/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 3.27/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.27/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.27/0.99      inference(light_normalisation,[status(thm)],[c_4455,c_3633]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_38,plain,
% 3.27/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_40,plain,
% 3.27/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_10,plain,
% 3.27/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1873,plain,
% 3.27/0.99      ( v1_funct_1(k2_funct_1(sK3)) | ~ v1_funct_1(sK3) | ~ v1_relat_1(sK3) ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1874,plain,
% 3.27/0.99      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 3.27/0.99      | v1_funct_1(sK3) != iProver_top
% 3.27/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1873]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_11,plain,
% 3.27/0.99      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.27/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1881,plain,
% 3.27/0.99      ( ~ v1_funct_1(sK3) | v1_relat_1(k2_funct_1(sK3)) | ~ v1_relat_1(sK3) ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1882,plain,
% 3.27/0.99      ( v1_funct_1(sK3) != iProver_top
% 3.27/0.99      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 3.27/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1881]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1893,plain,
% 3.27/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.27/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1892]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_5356,plain,
% 3.27/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_4509,c_38,c_40,c_1874,c_1882,c_1893]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_29,plain,
% 3.27/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.27/0.99      | v1_funct_2(X0,X1,X3)
% 3.27/0.99      | ~ r1_tarski(X2,X3)
% 3.27/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | ~ v1_funct_1(X0)
% 3.27/0.99      | k1_xboole_0 = X2 ),
% 3.27/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1620,plain,
% 3.27/0.99      ( k1_xboole_0 = X0
% 3.27/0.99      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.27/0.99      | v1_funct_2(X1,X2,X3) = iProver_top
% 3.27/0.99      | r1_tarski(X0,X3) != iProver_top
% 3.27/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.27/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_5366,plain,
% 3.27/0.99      ( k1_relat_1(sK3) = k1_xboole_0
% 3.27/0.99      | v1_funct_2(k2_funct_1(sK3),sK2,X0) = iProver_top
% 3.27/0.99      | v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) != iProver_top
% 3.27/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.27/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_5356,c_1620]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_24,plain,
% 3.27/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.27/0.99      | ~ v1_funct_1(X0)
% 3.27/0.99      | ~ v1_relat_1(X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1624,plain,
% 3.27/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 3.27/0.99      | v1_funct_1(X0) != iProver_top
% 3.27/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_4375,plain,
% 3.27/0.99      ( v1_funct_2(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)) = iProver_top
% 3.27/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.27/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1933,c_1624]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_4379,plain,
% 3.27/0.99      ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) = iProver_top
% 3.27/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.27/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.27/0.99      inference(light_normalisation,[status(thm)],[c_4375,c_3633]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7879,plain,
% 3.27/0.99      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.27/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 3.27/0.99      | v1_funct_2(k2_funct_1(sK3),sK2,X0) = iProver_top ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_5366,c_38,c_40,c_1874,c_1882,c_1893,c_4379]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7880,plain,
% 3.27/0.99      ( k1_relat_1(sK3) = k1_xboole_0
% 3.27/0.99      | v1_funct_2(k2_funct_1(sK3),sK2,X0) = iProver_top
% 3.27/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_7879]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_27,plain,
% 3.27/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.27/0.99      | ~ r1_tarski(X2,X3)
% 3.27/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.27/0.99      | ~ v1_funct_1(X0)
% 3.27/0.99      | k1_xboole_0 = X2 ),
% 3.27/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1622,plain,
% 3.27/0.99      ( k1_xboole_0 = X0
% 3.27/0.99      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.27/0.99      | r1_tarski(X0,X3) != iProver_top
% 3.27/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.27/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 3.27/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_5365,plain,
% 3.27/0.99      ( k1_relat_1(sK3) = k1_xboole_0
% 3.27/0.99      | v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) != iProver_top
% 3.27/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.27/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.27/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_5356,c_1622]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8030,plain,
% 3.27/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.27/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.27/0.99      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_5365,c_38,c_40,c_1874,c_1882,c_1893,c_4379]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8031,plain,
% 3.27/0.99      ( k1_relat_1(sK3) = k1_xboole_0
% 3.27/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.27/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_8030]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_32,negated_conjecture,
% 3.27/0.99      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.27/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.27/0.99      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 3.27/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1619,plain,
% 3.27/0.99      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 3.27/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.27/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_42,plain,
% 3.27/0.99      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 3.27/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.27/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1926,plain,
% 3.27/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.27/0.99      | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_1619,c_38,c_40,c_42,c_1874,c_1893]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1927,plain,
% 3.27/0.99      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 3.27/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_1926]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8043,plain,
% 3.27/0.99      ( k1_relat_1(sK3) = k1_xboole_0
% 3.27/0.99      | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 3.27/0.99      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_8031,c_1927]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_15,plain,
% 3.27/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.27/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_4,plain,
% 3.27/0.99      ( r1_tarski(k1_relat_1(X0),X1) | ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_421,plain,
% 3.27/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 3.27/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | ~ v1_relat_1(X0) ),
% 3.27/0.99      inference(resolution,[status(thm)],[c_15,c_4]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_425,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_421,c_15,c_14,c_4]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_426,plain,
% 3.27/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 3.27/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_425]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1955,plain,
% 3.27/0.99      ( r1_tarski(k1_relat_1(sK3),sK1)
% 3.27/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_426]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1956,plain,
% 3.27/0.99      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
% 3.27/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1955]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8098,plain,
% 3.27/0.99      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 3.27/0.99      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_8043,c_40,c_1956]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8099,plain,
% 3.27/0.99      ( k1_relat_1(sK3) = k1_xboole_0
% 3.27/0.99      | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_8098]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8104,plain,
% 3.27/0.99      ( k1_relat_1(sK3) = k1_xboole_0
% 3.27/0.99      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_7880,c_8099]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8203,plain,
% 3.27/0.99      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_8104,c_40,c_1956]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8,plain,
% 3.27/0.99      ( ~ v1_relat_1(X0)
% 3.27/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.27/0.99      | k1_relat_1(X0) = k1_xboole_0 ),
% 3.27/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1636,plain,
% 3.27/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.27/0.99      | k1_relat_1(X0) = k1_xboole_0
% 3.27/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3483,plain,
% 3.27/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0
% 3.27/0.99      | k1_relat_1(sK3) != k1_xboole_0
% 3.27/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1933,c_1636]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3487,plain,
% 3.27/0.99      ( k2_relat_1(sK3) = k1_xboole_0
% 3.27/0.99      | k1_relat_1(sK3) != k1_xboole_0
% 3.27/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_3483,c_1996]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_9,plain,
% 3.27/0.99      ( ~ v1_relat_1(X0)
% 3.27/0.99      | k2_relat_1(X0) = k1_xboole_0
% 3.27/0.99      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.27/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2526,plain,
% 3.27/0.99      ( ~ v1_relat_1(sK3)
% 3.27/0.99      | k2_relat_1(sK3) = k1_xboole_0
% 3.27/0.99      | k1_relat_1(sK3) != k1_xboole_0 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_4037,plain,
% 3.27/0.99      ( k1_relat_1(sK3) != k1_xboole_0 | k2_relat_1(sK3) = k1_xboole_0 ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_3487,c_35,c_1892,c_2526]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_4038,plain,
% 3.27/0.99      ( k2_relat_1(sK3) = k1_xboole_0 | k1_relat_1(sK3) != k1_xboole_0 ),
% 3.27/0.99      inference(renaming,[status(thm)],[c_4037]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_4039,plain,
% 3.27/0.99      ( k1_relat_1(sK3) != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_4038,c_3504]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8222,plain,
% 3.27/0.99      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_8203,c_4039]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8235,plain,
% 3.27/0.99      ( sK2 = k1_xboole_0 ),
% 3.27/0.99      inference(equality_resolution_simp,[status(thm)],[c_8222]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_7,plain,
% 3.27/0.99      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.27/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1637,plain,
% 3.27/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 3.27/0.99      | k1_xboole_0 = X0
% 3.27/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8264,plain,
% 3.27/0.99      ( sK3 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_8203,c_1637]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2082,plain,
% 3.27/0.99      ( ~ v1_relat_1(sK3)
% 3.27/0.99      | k1_relat_1(sK3) != k1_xboole_0
% 3.27/0.99      | k1_xboole_0 = sK3 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1058,plain,( X0 = X0 ),theory(equality) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2130,plain,
% 3.27/0.99      ( sK3 = sK3 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_1058]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1059,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2274,plain,
% 3.27/0.99      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_1059]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3067,plain,
% 3.27/0.99      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_2274]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3068,plain,
% 3.27/0.99      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_3067]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8304,plain,
% 3.27/0.99      ( sK3 = k1_xboole_0 ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_8264,c_35,c_40,c_1892,c_1956,c_2082,c_2130,c_3068,c_8104]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8320,plain,
% 3.27/0.99      ( v1_funct_2(k2_funct_1(k1_xboole_0),sK2,sK1) != iProver_top
% 3.27/0.99      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_8304,c_1927]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_9024,plain,
% 3.27/0.99      ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) != iProver_top
% 3.27/0.99      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_8235,c_8320]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8317,plain,
% 3.27/0.99      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = sK2 ),
% 3.27/0.99      inference(demodulation,[status(thm)],[c_8304,c_3633]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_8811,plain,
% 3.27/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0
% 3.27/0.99      | sK2 != k1_xboole_0
% 3.27/0.99      | v1_relat_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_8317,c_1637]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_22,plain,
% 3.27/0.99      ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.27/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_57,plain,
% 3.27/0.99      ( m1_subset_1(sK0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_19,plain,
% 3.27/0.99      ( v1_funct_1(sK0(X0,X1)) ),
% 3.27/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_65,plain,
% 3.27/0.99      ( v1_funct_1(sK0(X0,X1)) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_67,plain,
% 3.27/0.99      ( v1_funct_1(sK0(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_65]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_87,plain,
% 3.27/0.99      ( v1_funct_1(X0) != iProver_top
% 3.27/0.99      | v1_relat_1(X0) != iProver_top
% 3.27/0.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_89,plain,
% 3.27/0.99      ( v1_funct_1(k1_xboole_0) != iProver_top
% 3.27/0.99      | v1_relat_1(k2_funct_1(k1_xboole_0)) = iProver_top
% 3.27/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_87]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_0,plain,
% 3.27/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1884,plain,
% 3.27/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.27/0.99      | v1_relat_1(k1_xboole_0) ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1886,plain,
% 3.27/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.27/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1884]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2,plain,
% 3.27/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.27/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1885,plain,
% 3.27/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1888,plain,
% 3.27/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1885]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1068,plain,
% 3.27/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.27/0.99      theory(equality) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1915,plain,
% 3.27/0.99      ( v1_funct_1(X0) | ~ v1_funct_1(sK0(X1,X2)) | X0 != sK0(X1,X2) ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_1068]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1916,plain,
% 3.27/0.99      ( X0 != sK0(X1,X2)
% 3.27/0.99      | v1_funct_1(X0) = iProver_top
% 3.27/0.99      | v1_funct_1(sK0(X1,X2)) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1915]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1918,plain,
% 3.27/0.99      ( k1_xboole_0 != sK0(k1_xboole_0,k1_xboole_0)
% 3.27/0.99      | v1_funct_1(sK0(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.27/0.99      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_1916]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1,plain,
% 3.27/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.27/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2346,plain,
% 3.27/0.99      ( ~ v1_xboole_0(sK0(X0,X1)) | k1_xboole_0 = sK0(X0,X1) ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_2350,plain,
% 3.27/0.99      ( ~ v1_xboole_0(sK0(k1_xboole_0,k1_xboole_0))
% 3.27/0.99      | k1_xboole_0 = sK0(k1_xboole_0,k1_xboole_0) ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_2346]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_16,plain,
% 3.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/0.99      | ~ v1_xboole_0(X1)
% 3.27/0.99      | v1_xboole_0(X0) ),
% 3.27/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3265,plain,
% 3.27/0.99      ( ~ m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.27/0.99      | ~ v1_xboole_0(X2)
% 3.27/0.99      | v1_xboole_0(sK0(X0,X1)) ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_3267,plain,
% 3.27/0.99      ( ~ m1_subset_1(sK0(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 3.27/0.99      | v1_xboole_0(sK0(k1_xboole_0,k1_xboole_0))
% 3.27/0.99      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.27/0.99      inference(instantiation,[status(thm)],[c_3265]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_9451,plain,
% 3.27/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.27/0.99      inference(global_propositional_subsumption,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_8811,c_40,c_57,c_67,c_89,c_0,c_1886,c_1888,c_1918,c_1956,
% 3.27/0.99                 c_2350,c_3267,c_4039,c_8104]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_9457,plain,
% 3.27/0.99      ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) != iProver_top
% 3.27/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.27/0.99      inference(light_normalisation,[status(thm)],[c_9024,c_9451]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1640,plain,
% 3.27/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1642,plain,
% 3.27/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1626,plain,
% 3.27/0.99      ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1631,plain,
% 3.27/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.27/0.99      | v1_xboole_0(X1) != iProver_top
% 3.27/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_4412,plain,
% 3.27/0.99      ( v1_xboole_0(X0) != iProver_top
% 3.27/0.99      | v1_xboole_0(sK0(X0,X1)) = iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1626,c_1631]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1641,plain,
% 3.27/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_5194,plain,
% 3.27/0.99      ( sK0(X0,X1) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_4412,c_1641]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_5219,plain,
% 3.27/0.99      ( sK0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_1642,c_5194]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_18,plain,
% 3.27/0.99      ( v1_funct_2(sK0(X0,X1),X0,X1) ),
% 3.27/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_1629,plain,
% 3.27/0.99      ( v1_funct_2(sK0(X0,X1),X0,X1) = iProver_top ),
% 3.27/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_6022,plain,
% 3.27/0.99      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 3.27/0.99      inference(superposition,[status(thm)],[c_5219,c_1629]) ).
% 3.27/0.99  
% 3.27/0.99  cnf(c_9460,plain,
% 3.27/0.99      ( $false ),
% 3.27/0.99      inference(forward_subsumption_resolution,
% 3.27/0.99                [status(thm)],
% 3.27/0.99                [c_9457,c_1640,c_6022]) ).
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  ------                               Statistics
% 3.27/0.99  
% 3.27/0.99  ------ General
% 3.27/0.99  
% 3.27/0.99  abstr_ref_over_cycles:                  0
% 3.27/0.99  abstr_ref_under_cycles:                 0
% 3.27/0.99  gc_basic_clause_elim:                   0
% 3.27/0.99  forced_gc_time:                         0
% 3.27/0.99  parsing_time:                           0.01
% 3.27/0.99  unif_index_cands_time:                  0.
% 3.27/0.99  unif_index_add_time:                    0.
% 3.27/0.99  orderings_time:                         0.
% 3.27/0.99  out_proof_time:                         0.012
% 3.27/0.99  total_time:                             0.287
% 3.27/0.99  num_of_symbols:                         50
% 3.27/0.99  num_of_terms:                           8919
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing
% 3.27/0.99  
% 3.27/0.99  num_of_splits:                          0
% 3.27/0.99  num_of_split_atoms:                     0
% 3.27/0.99  num_of_reused_defs:                     0
% 3.27/0.99  num_eq_ax_congr_red:                    10
% 3.27/0.99  num_of_sem_filtered_clauses:            1
% 3.27/0.99  num_of_subtypes:                        0
% 3.27/0.99  monotx_restored_types:                  0
% 3.27/0.99  sat_num_of_epr_types:                   0
% 3.27/0.99  sat_num_of_non_cyclic_types:            0
% 3.27/0.99  sat_guarded_non_collapsed_types:        0
% 3.27/0.99  num_pure_diseq_elim:                    0
% 3.27/0.99  simp_replaced_by:                       0
% 3.27/0.99  res_preprocessed:                       160
% 3.27/0.99  prep_upred:                             0
% 3.27/0.99  prep_unflattend:                        36
% 3.27/0.99  smt_new_axioms:                         0
% 3.27/0.99  pred_elim_cands:                        6
% 3.27/0.99  pred_elim:                              2
% 3.27/0.99  pred_elim_cl:                           3
% 3.27/0.99  pred_elim_cycles:                       4
% 3.27/0.99  merged_defs:                            0
% 3.27/0.99  merged_defs_ncl:                        0
% 3.27/0.99  bin_hyper_res:                          0
% 3.27/0.99  prep_cycles:                            4
% 3.27/0.99  pred_elim_time:                         0.01
% 3.27/0.99  splitting_time:                         0.
% 3.27/0.99  sem_filter_time:                        0.
% 3.27/0.99  monotx_time:                            0.001
% 3.27/0.99  subtype_inf_time:                       0.
% 3.27/0.99  
% 3.27/0.99  ------ Problem properties
% 3.27/0.99  
% 3.27/0.99  clauses:                                32
% 3.27/0.99  conjectures:                            5
% 3.27/0.99  epr:                                    4
% 3.27/0.99  horn:                                   30
% 3.27/0.99  ground:                                 8
% 3.27/0.99  unary:                                  11
% 3.27/0.99  binary:                                 7
% 3.27/0.99  lits:                                   77
% 3.27/0.99  lits_eq:                                15
% 3.27/0.99  fd_pure:                                0
% 3.27/0.99  fd_pseudo:                              0
% 3.27/0.99  fd_cond:                                5
% 3.27/0.99  fd_pseudo_cond:                         0
% 3.27/0.99  ac_symbols:                             0
% 3.27/0.99  
% 3.27/0.99  ------ Propositional Solver
% 3.27/0.99  
% 3.27/0.99  prop_solver_calls:                      29
% 3.27/0.99  prop_fast_solver_calls:                 1260
% 3.27/0.99  smt_solver_calls:                       0
% 3.27/0.99  smt_fast_solver_calls:                  0
% 3.27/0.99  prop_num_of_clauses:                    3498
% 3.27/0.99  prop_preprocess_simplified:             8996
% 3.27/0.99  prop_fo_subsumed:                       55
% 3.27/0.99  prop_solver_time:                       0.
% 3.27/0.99  smt_solver_time:                        0.
% 3.27/0.99  smt_fast_solver_time:                   0.
% 3.27/0.99  prop_fast_solver_time:                  0.
% 3.27/0.99  prop_unsat_core_time:                   0.
% 3.27/0.99  
% 3.27/0.99  ------ QBF
% 3.27/0.99  
% 3.27/0.99  qbf_q_res:                              0
% 3.27/0.99  qbf_num_tautologies:                    0
% 3.27/0.99  qbf_prep_cycles:                        0
% 3.27/0.99  
% 3.27/0.99  ------ BMC1
% 3.27/0.99  
% 3.27/0.99  bmc1_current_bound:                     -1
% 3.27/0.99  bmc1_last_solved_bound:                 -1
% 3.27/0.99  bmc1_unsat_core_size:                   -1
% 3.27/0.99  bmc1_unsat_core_parents_size:           -1
% 3.27/0.99  bmc1_merge_next_fun:                    0
% 3.27/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation
% 3.27/0.99  
% 3.27/0.99  inst_num_of_clauses:                    1022
% 3.27/0.99  inst_num_in_passive:                    267
% 3.27/0.99  inst_num_in_active:                     511
% 3.27/0.99  inst_num_in_unprocessed:                244
% 3.27/0.99  inst_num_of_loops:                      560
% 3.27/0.99  inst_num_of_learning_restarts:          0
% 3.27/0.99  inst_num_moves_active_passive:          46
% 3.27/0.99  inst_lit_activity:                      0
% 3.27/0.99  inst_lit_activity_moves:                0
% 3.27/0.99  inst_num_tautologies:                   0
% 3.27/0.99  inst_num_prop_implied:                  0
% 3.27/0.99  inst_num_existing_simplified:           0
% 3.27/0.99  inst_num_eq_res_simplified:             0
% 3.27/0.99  inst_num_child_elim:                    0
% 3.27/0.99  inst_num_of_dismatching_blockings:      542
% 3.27/0.99  inst_num_of_non_proper_insts:           980
% 3.27/0.99  inst_num_of_duplicates:                 0
% 3.27/0.99  inst_inst_num_from_inst_to_res:         0
% 3.27/0.99  inst_dismatching_checking_time:         0.
% 3.27/0.99  
% 3.27/0.99  ------ Resolution
% 3.27/0.99  
% 3.27/0.99  res_num_of_clauses:                     0
% 3.27/0.99  res_num_in_passive:                     0
% 3.27/0.99  res_num_in_active:                      0
% 3.27/0.99  res_num_of_loops:                       164
% 3.27/0.99  res_forward_subset_subsumed:            37
% 3.27/0.99  res_backward_subset_subsumed:           2
% 3.27/0.99  res_forward_subsumed:                   0
% 3.27/0.99  res_backward_subsumed:                  0
% 3.27/0.99  res_forward_subsumption_resolution:     0
% 3.27/0.99  res_backward_subsumption_resolution:    0
% 3.27/0.99  res_clause_to_clause_subsumption:       499
% 3.27/0.99  res_orphan_elimination:                 0
% 3.27/0.99  res_tautology_del:                      139
% 3.27/0.99  res_num_eq_res_simplified:              0
% 3.27/0.99  res_num_sel_changes:                    0
% 3.27/0.99  res_moves_from_active_to_pass:          0
% 3.27/0.99  
% 3.27/0.99  ------ Superposition
% 3.27/0.99  
% 3.27/0.99  sup_time_total:                         0.
% 3.27/0.99  sup_time_generating:                    0.
% 3.27/0.99  sup_time_sim_full:                      0.
% 3.27/0.99  sup_time_sim_immed:                     0.
% 3.27/0.99  
% 3.27/0.99  sup_num_of_clauses:                     99
% 3.27/0.99  sup_num_in_active:                      52
% 3.27/0.99  sup_num_in_passive:                     47
% 3.27/0.99  sup_num_of_loops:                       111
% 3.27/0.99  sup_fw_superposition:                   88
% 3.27/0.99  sup_bw_superposition:                   98
% 3.27/0.99  sup_immediate_simplified:               110
% 3.27/0.99  sup_given_eliminated:                   0
% 3.27/0.99  comparisons_done:                       0
% 3.27/0.99  comparisons_avoided:                    0
% 3.27/0.99  
% 3.27/0.99  ------ Simplifications
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  sim_fw_subset_subsumed:                 36
% 3.27/0.99  sim_bw_subset_subsumed:                 15
% 3.27/0.99  sim_fw_subsumed:                        16
% 3.27/0.99  sim_bw_subsumed:                        0
% 3.27/0.99  sim_fw_subsumption_res:                 4
% 3.27/0.99  sim_bw_subsumption_res:                 0
% 3.27/0.99  sim_tautology_del:                      5
% 3.27/0.99  sim_eq_tautology_del:                   19
% 3.27/0.99  sim_eq_res_simp:                        2
% 3.27/0.99  sim_fw_demodulated:                     7
% 3.27/0.99  sim_bw_demodulated:                     49
% 3.27/0.99  sim_light_normalised:                   57
% 3.27/0.99  sim_joinable_taut:                      0
% 3.27/0.99  sim_joinable_simp:                      0
% 3.27/0.99  sim_ac_normalised:                      0
% 3.27/0.99  sim_smt_subsumption:                    0
% 3.27/0.99  
%------------------------------------------------------------------------------
