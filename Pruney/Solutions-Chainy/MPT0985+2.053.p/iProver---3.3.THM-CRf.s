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
% DateTime   : Thu Dec  3 12:02:30 EST 2020

% Result     : Theorem 7.48s
% Output     : CNFRefutation 7.48s
% Verified   : 
% Statistics : Number of formulae       :  266 (3414 expanded)
%              Number of clauses        :  166 (1209 expanded)
%              Number of leaves         :   26 ( 661 expanded)
%              Depth                    :   25
%              Number of atoms          :  708 (14878 expanded)
%              Number of equality atoms :  321 (3105 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f36,conjecture,(
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

fof(f37,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f36])).

fof(f75,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f76,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f75])).

fof(f84,plain,
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

fof(f85,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f76,f84])).

fof(f144,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f85])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f32,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f131,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f35,axiom,(
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

fof(f73,plain,(
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
    inference(ennf_transformation,[],[f35])).

fof(f74,plain,(
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
    inference(flattening,[],[f73])).

fof(f140,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f116,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f132,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f33])).

fof(f152,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f116,f132])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f69])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f130,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f32])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f108,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f148,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f108,f132])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f29])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f97,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f146,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f85])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f104,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f102,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f34,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f71])).

fof(f135,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f101,plain,(
    ! [X0] :
      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f142,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f112,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f145,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f114,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f83,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f105,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f134,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f147,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f85])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f107,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f149,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f107,f132])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f77])).

fof(f79,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f78,f79])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f17,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f110,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f151,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f110,f132])).

fof(f22,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f117,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f155,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f117,f132])).

fof(f103,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 != X0
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f159,plain,(
    ! [X2,X3,X1] :
      ( v1_funct_2(X3,k1_xboole_0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f139])).

cnf(c_58,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_4205,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_4240,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6406,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4205,c_4240])).

cnf(c_44,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_4214,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_50,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_4210,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_7758,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(k6_partfun1(X0),X0,X0) != iProver_top
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_funct_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4214,c_4210])).

cnf(c_29,plain,
    ( v1_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_123,plain,
    ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_42,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_45,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_718,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | X3 != X1
    | k6_partfun1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_45])).

cnf(c_719,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X1)
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(k6_partfun1(X0)) ),
    inference(unflattening,[status(thm)],[c_718])).

cnf(c_723,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_2(k6_partfun1(X0),X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_719,c_29])).

cnf(c_724,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X1)
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(renaming,[status(thm)],[c_723])).

cnf(c_4200,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X1) = iProver_top
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_724])).

cnf(c_5540,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4214,c_4200])).

cnf(c_29255,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7758,c_123,c_5540])).

cnf(c_29256,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_29255])).

cnf(c_41,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_4215,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_29268,plain,
    ( k2_relset_1(X0,X1,k6_partfun1(X0)) = k2_relat_1(k6_partfun1(X0))
    | k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_29256,c_4215])).

cnf(c_21,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f148])).

cnf(c_29303,plain,
    ( k2_relset_1(X0,X1,k6_partfun1(X0)) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29268,c_21])).

cnf(c_29326,plain,
    ( k2_relset_1(sK3,k2_zfmisc_1(sK1,sK2),k6_partfun1(sK3)) = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6406,c_29303])).

cnf(c_63,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_4704,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_4705,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4704])).

cnf(c_40,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_739,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_40,c_10])).

cnf(c_743,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_739,c_39])).

cnf(c_744,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_743])).

cnf(c_4781,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_744])).

cnf(c_4782,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4781])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_4915,plain,
    ( v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4928,plain,
    ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4915])).

cnf(c_5447,plain,
    ( v1_relat_1(k4_relat_1(k4_relat_1(sK3)))
    | ~ v1_relat_1(k4_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_5460,plain,
    ( v1_relat_1(k4_relat_1(k4_relat_1(sK3))) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5447])).

cnf(c_9199,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4205,c_4215])).

cnf(c_56,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f146])).

cnf(c_9233,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_9199,c_56])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_4233,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9291,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9233,c_4233])).

cnf(c_9439,plain,
    ( sK3 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9291,c_63,c_4705])).

cnf(c_9440,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_9439])).

cnf(c_4216,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_6743,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4205,c_4216])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_4235,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7174,plain,
    ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_6743,c_4235])).

cnf(c_46,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_4213,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_10174,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7174,c_4213])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_4234,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7175,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_6743,c_4234])).

cnf(c_9281,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_9233,c_7175])).

cnf(c_10223,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10174,c_9281])).

cnf(c_60,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_61,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_4203,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_26,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_4227,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_11522,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4203,c_4227])).

cnf(c_57,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_917,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_57])).

cnf(c_918,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_917])).

cnf(c_11889,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11522,c_60,c_58,c_918,c_4704])).

cnf(c_27,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_4226,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_11907,plain,
    ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11889,c_4226])).

cnf(c_14814,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10223,c_61,c_63,c_4705,c_4928,c_11907])).

cnf(c_14820,plain,
    ( v1_relat_1(k4_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14814,c_4216])).

cnf(c_15322,plain,
    ( k1_relat_1(k4_relat_1(k4_relat_1(sK3))) = k2_relat_1(k4_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_14820,c_4234])).

cnf(c_15328,plain,
    ( k1_relat_1(k4_relat_1(k4_relat_1(sK3))) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_15322,c_7174])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_4230,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_15697,plain,
    ( k2_relat_1(k4_relat_1(k4_relat_1(sK3))) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k4_relat_1(k4_relat_1(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15328,c_4230])).

cnf(c_15321,plain,
    ( k2_relat_1(k4_relat_1(k4_relat_1(sK3))) = k1_relat_1(k4_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_14820,c_4235])).

cnf(c_15331,plain,
    ( k2_relat_1(k4_relat_1(k4_relat_1(sK3))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_15321,c_9281])).

cnf(c_15708,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_relat_1(k4_relat_1(k4_relat_1(sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15697,c_15331])).

cnf(c_52,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f138])).

cnf(c_4208,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_14824,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK3),sK2,X0) = iProver_top
    | v1_funct_2(k4_relat_1(sK3),sK2,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14814,c_4208])).

cnf(c_47,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_4212,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_9729,plain,
    ( v1_funct_2(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3)),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7174,c_4212])).

cnf(c_9733,plain,
    ( v1_funct_2(k4_relat_1(sK3),sK2,k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9729,c_9281])).

cnf(c_29048,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK3),sK2,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14824,c_61,c_63,c_4705,c_4928,c_9733,c_11907])).

cnf(c_29049,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK3),sK2,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_29048])).

cnf(c_14823,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK3),sK2,k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14814,c_4210])).

cnf(c_29168,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14823,c_61,c_63,c_4705,c_4928,c_9733,c_11907])).

cnf(c_29169,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_29168])).

cnf(c_55,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_4207,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_11894,plain,
    ( v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11889,c_4207])).

cnf(c_11924,plain,
    ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11894,c_61,c_63,c_4705,c_11907])).

cnf(c_11925,plain,
    ( v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11924])).

cnf(c_29183,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_29169,c_11925])).

cnf(c_29246,plain,
    ( v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29183,c_63,c_4782])).

cnf(c_29247,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_29246])).

cnf(c_29252,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_29049,c_29247])).

cnf(c_29414,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29326,c_63,c_4705,c_4782,c_4928,c_5460,c_9440,c_15708,c_29252])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_4241,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6431,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4241,c_4207])).

cnf(c_4630,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_4631,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4630])).

cnf(c_6522,plain,
    ( r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6431,c_61,c_63,c_4631,c_4705])).

cnf(c_6523,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6522])).

cnf(c_11893,plain,
    ( v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top
    | r1_tarski(k4_relat_1(sK3),k2_zfmisc_1(sK2,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11889,c_6523])).

cnf(c_29523,plain,
    ( v1_funct_2(k4_relat_1(k1_xboole_0),sK2,sK1) != iProver_top
    | r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(sK2,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29414,c_11893])).

cnf(c_29563,plain,
    ( k2_relset_1(sK1,sK2,k1_xboole_0) = sK2 ),
    inference(demodulation,[status(thm)],[c_29414,c_56])).

cnf(c_4199,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_5539,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4214,c_4199])).

cnf(c_22,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f149])).

cnf(c_5544,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5539,c_22])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4244,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_438,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_439,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_438])).

cnf(c_524,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_439])).

cnf(c_703,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_524])).

cnf(c_704,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_703])).

cnf(c_4201,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_6469,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4244,c_4201])).

cnf(c_6638,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5544,c_6469])).

cnf(c_9197,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4241,c_4215])).

cnf(c_25359,plain,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6638,c_9197])).

cnf(c_24,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f151])).

cnf(c_4790,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_24,c_21])).

cnf(c_25381,plain,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_25359,c_4790])).

cnf(c_29565,plain,
    ( sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_29563,c_25381])).

cnf(c_29617,plain,
    ( v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK1) != iProver_top
    | r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29523,c_29565])).

cnf(c_32,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f155])).

cnf(c_4223,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5179,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_4223])).

cnf(c_5873,plain,
    ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5179,c_4234])).

cnf(c_5875,plain,
    ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5873,c_4790])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_4232,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7145,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5875,c_4232])).

cnf(c_170,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_172,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_170])).

cnf(c_17141,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7145,c_172,c_5179])).

cnf(c_29620,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) != iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29617,c_17141])).

cnf(c_5436,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_4200])).

cnf(c_5437,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5436,c_24])).

cnf(c_4224,plain,
    ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5287,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_4224])).

cnf(c_5439,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5437])).

cnf(c_5538,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_4214])).

cnf(c_51,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_funct_2(X0,k1_xboole_0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_tarski(X1,X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_4209,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_6702,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5538,c_4209])).

cnf(c_7923,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5437,c_5287,c_5439,c_5538,c_6638,c_6702])).

cnf(c_30462,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_29620,c_6638,c_7923])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n022.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 18:10:40 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 7.48/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.48/1.48  
% 7.48/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.48/1.48  
% 7.48/1.48  ------  iProver source info
% 7.48/1.48  
% 7.48/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.48/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.48/1.48  git: non_committed_changes: false
% 7.48/1.48  git: last_make_outside_of_git: false
% 7.48/1.48  
% 7.48/1.48  ------ 
% 7.48/1.48  
% 7.48/1.48  ------ Input Options
% 7.48/1.48  
% 7.48/1.48  --out_options                           all
% 7.48/1.48  --tptp_safe_out                         true
% 7.48/1.48  --problem_path                          ""
% 7.48/1.48  --include_path                          ""
% 7.48/1.48  --clausifier                            res/vclausify_rel
% 7.48/1.48  --clausifier_options                    --mode clausify
% 7.48/1.48  --stdin                                 false
% 7.48/1.48  --stats_out                             all
% 7.48/1.48  
% 7.48/1.48  ------ General Options
% 7.48/1.48  
% 7.48/1.48  --fof                                   false
% 7.48/1.48  --time_out_real                         305.
% 7.48/1.48  --time_out_virtual                      -1.
% 7.48/1.48  --symbol_type_check                     false
% 7.48/1.48  --clausify_out                          false
% 7.48/1.48  --sig_cnt_out                           false
% 7.48/1.48  --trig_cnt_out                          false
% 7.48/1.48  --trig_cnt_out_tolerance                1.
% 7.48/1.48  --trig_cnt_out_sk_spl                   false
% 7.48/1.48  --abstr_cl_out                          false
% 7.48/1.48  
% 7.48/1.48  ------ Global Options
% 7.48/1.48  
% 7.48/1.48  --schedule                              default
% 7.48/1.48  --add_important_lit                     false
% 7.48/1.48  --prop_solver_per_cl                    1000
% 7.48/1.48  --min_unsat_core                        false
% 7.48/1.48  --soft_assumptions                      false
% 7.48/1.48  --soft_lemma_size                       3
% 7.48/1.48  --prop_impl_unit_size                   0
% 7.48/1.48  --prop_impl_unit                        []
% 7.48/1.48  --share_sel_clauses                     true
% 7.48/1.48  --reset_solvers                         false
% 7.48/1.48  --bc_imp_inh                            [conj_cone]
% 7.48/1.48  --conj_cone_tolerance                   3.
% 7.48/1.48  --extra_neg_conj                        none
% 7.48/1.48  --large_theory_mode                     true
% 7.48/1.48  --prolific_symb_bound                   200
% 7.48/1.48  --lt_threshold                          2000
% 7.48/1.48  --clause_weak_htbl                      true
% 7.48/1.48  --gc_record_bc_elim                     false
% 7.48/1.48  
% 7.48/1.48  ------ Preprocessing Options
% 7.48/1.48  
% 7.48/1.48  --preprocessing_flag                    true
% 7.48/1.48  --time_out_prep_mult                    0.1
% 7.48/1.48  --splitting_mode                        input
% 7.48/1.48  --splitting_grd                         true
% 7.48/1.48  --splitting_cvd                         false
% 7.48/1.48  --splitting_cvd_svl                     false
% 7.48/1.48  --splitting_nvd                         32
% 7.48/1.48  --sub_typing                            true
% 7.48/1.48  --prep_gs_sim                           true
% 7.48/1.48  --prep_unflatten                        true
% 7.48/1.48  --prep_res_sim                          true
% 7.48/1.48  --prep_upred                            true
% 7.48/1.48  --prep_sem_filter                       exhaustive
% 7.48/1.48  --prep_sem_filter_out                   false
% 7.48/1.48  --pred_elim                             true
% 7.48/1.48  --res_sim_input                         true
% 7.48/1.48  --eq_ax_congr_red                       true
% 7.48/1.48  --pure_diseq_elim                       true
% 7.48/1.48  --brand_transform                       false
% 7.48/1.48  --non_eq_to_eq                          false
% 7.48/1.48  --prep_def_merge                        true
% 7.48/1.48  --prep_def_merge_prop_impl              false
% 7.48/1.48  --prep_def_merge_mbd                    true
% 7.48/1.48  --prep_def_merge_tr_red                 false
% 7.48/1.48  --prep_def_merge_tr_cl                  false
% 7.48/1.48  --smt_preprocessing                     true
% 7.48/1.48  --smt_ac_axioms                         fast
% 7.48/1.48  --preprocessed_out                      false
% 7.48/1.48  --preprocessed_stats                    false
% 7.48/1.48  
% 7.48/1.48  ------ Abstraction refinement Options
% 7.48/1.48  
% 7.48/1.48  --abstr_ref                             []
% 7.48/1.48  --abstr_ref_prep                        false
% 7.48/1.48  --abstr_ref_until_sat                   false
% 7.48/1.48  --abstr_ref_sig_restrict                funpre
% 7.48/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.48/1.48  --abstr_ref_under                       []
% 7.48/1.48  
% 7.48/1.48  ------ SAT Options
% 7.48/1.48  
% 7.48/1.48  --sat_mode                              false
% 7.48/1.48  --sat_fm_restart_options                ""
% 7.48/1.48  --sat_gr_def                            false
% 7.48/1.48  --sat_epr_types                         true
% 7.48/1.48  --sat_non_cyclic_types                  false
% 7.48/1.48  --sat_finite_models                     false
% 7.48/1.48  --sat_fm_lemmas                         false
% 7.48/1.48  --sat_fm_prep                           false
% 7.48/1.48  --sat_fm_uc_incr                        true
% 7.48/1.48  --sat_out_model                         small
% 7.48/1.48  --sat_out_clauses                       false
% 7.48/1.48  
% 7.48/1.48  ------ QBF Options
% 7.48/1.48  
% 7.48/1.48  --qbf_mode                              false
% 7.48/1.48  --qbf_elim_univ                         false
% 7.48/1.48  --qbf_dom_inst                          none
% 7.48/1.48  --qbf_dom_pre_inst                      false
% 7.48/1.48  --qbf_sk_in                             false
% 7.48/1.48  --qbf_pred_elim                         true
% 7.48/1.48  --qbf_split                             512
% 7.48/1.48  
% 7.48/1.48  ------ BMC1 Options
% 7.48/1.48  
% 7.48/1.48  --bmc1_incremental                      false
% 7.48/1.48  --bmc1_axioms                           reachable_all
% 7.48/1.48  --bmc1_min_bound                        0
% 7.48/1.48  --bmc1_max_bound                        -1
% 7.48/1.48  --bmc1_max_bound_default                -1
% 7.48/1.48  --bmc1_symbol_reachability              true
% 7.48/1.48  --bmc1_property_lemmas                  false
% 7.48/1.48  --bmc1_k_induction                      false
% 7.48/1.48  --bmc1_non_equiv_states                 false
% 7.48/1.48  --bmc1_deadlock                         false
% 7.48/1.48  --bmc1_ucm                              false
% 7.48/1.48  --bmc1_add_unsat_core                   none
% 7.48/1.48  --bmc1_unsat_core_children              false
% 7.48/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.48/1.48  --bmc1_out_stat                         full
% 7.48/1.48  --bmc1_ground_init                      false
% 7.48/1.48  --bmc1_pre_inst_next_state              false
% 7.48/1.48  --bmc1_pre_inst_state                   false
% 7.48/1.48  --bmc1_pre_inst_reach_state             false
% 7.48/1.48  --bmc1_out_unsat_core                   false
% 7.48/1.48  --bmc1_aig_witness_out                  false
% 7.48/1.48  --bmc1_verbose                          false
% 7.48/1.48  --bmc1_dump_clauses_tptp                false
% 7.48/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.48/1.48  --bmc1_dump_file                        -
% 7.48/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.48/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.48/1.48  --bmc1_ucm_extend_mode                  1
% 7.48/1.48  --bmc1_ucm_init_mode                    2
% 7.48/1.48  --bmc1_ucm_cone_mode                    none
% 7.48/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.48/1.48  --bmc1_ucm_relax_model                  4
% 7.48/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.48/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.48/1.48  --bmc1_ucm_layered_model                none
% 7.48/1.48  --bmc1_ucm_max_lemma_size               10
% 7.48/1.48  
% 7.48/1.48  ------ AIG Options
% 7.48/1.48  
% 7.48/1.48  --aig_mode                              false
% 7.48/1.48  
% 7.48/1.48  ------ Instantiation Options
% 7.48/1.48  
% 7.48/1.48  --instantiation_flag                    true
% 7.48/1.48  --inst_sos_flag                         false
% 7.48/1.48  --inst_sos_phase                        true
% 7.48/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.48/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.48/1.48  --inst_lit_sel_side                     num_symb
% 7.48/1.48  --inst_solver_per_active                1400
% 7.48/1.48  --inst_solver_calls_frac                1.
% 7.48/1.48  --inst_passive_queue_type               priority_queues
% 7.48/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.48/1.48  --inst_passive_queues_freq              [25;2]
% 7.48/1.48  --inst_dismatching                      true
% 7.48/1.48  --inst_eager_unprocessed_to_passive     true
% 7.48/1.48  --inst_prop_sim_given                   true
% 7.48/1.48  --inst_prop_sim_new                     false
% 7.48/1.48  --inst_subs_new                         false
% 7.48/1.48  --inst_eq_res_simp                      false
% 7.48/1.48  --inst_subs_given                       false
% 7.48/1.48  --inst_orphan_elimination               true
% 7.48/1.48  --inst_learning_loop_flag               true
% 7.48/1.48  --inst_learning_start                   3000
% 7.48/1.48  --inst_learning_factor                  2
% 7.48/1.48  --inst_start_prop_sim_after_learn       3
% 7.48/1.48  --inst_sel_renew                        solver
% 7.48/1.48  --inst_lit_activity_flag                true
% 7.48/1.48  --inst_restr_to_given                   false
% 7.48/1.48  --inst_activity_threshold               500
% 7.48/1.48  --inst_out_proof                        true
% 7.48/1.48  
% 7.48/1.48  ------ Resolution Options
% 7.48/1.48  
% 7.48/1.48  --resolution_flag                       true
% 7.48/1.48  --res_lit_sel                           adaptive
% 7.48/1.48  --res_lit_sel_side                      none
% 7.48/1.48  --res_ordering                          kbo
% 7.48/1.48  --res_to_prop_solver                    active
% 7.48/1.48  --res_prop_simpl_new                    false
% 7.48/1.48  --res_prop_simpl_given                  true
% 7.48/1.48  --res_passive_queue_type                priority_queues
% 7.48/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.48/1.48  --res_passive_queues_freq               [15;5]
% 7.48/1.48  --res_forward_subs                      full
% 7.48/1.48  --res_backward_subs                     full
% 7.48/1.48  --res_forward_subs_resolution           true
% 7.48/1.48  --res_backward_subs_resolution          true
% 7.48/1.48  --res_orphan_elimination                true
% 7.48/1.48  --res_time_limit                        2.
% 7.48/1.48  --res_out_proof                         true
% 7.48/1.48  
% 7.48/1.48  ------ Superposition Options
% 7.48/1.48  
% 7.48/1.48  --superposition_flag                    true
% 7.48/1.48  --sup_passive_queue_type                priority_queues
% 7.48/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.48/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.48/1.48  --demod_completeness_check              fast
% 7.48/1.48  --demod_use_ground                      true
% 7.48/1.48  --sup_to_prop_solver                    passive
% 7.48/1.48  --sup_prop_simpl_new                    true
% 7.48/1.48  --sup_prop_simpl_given                  true
% 7.48/1.48  --sup_fun_splitting                     false
% 7.48/1.48  --sup_smt_interval                      50000
% 7.48/1.48  
% 7.48/1.48  ------ Superposition Simplification Setup
% 7.48/1.48  
% 7.48/1.48  --sup_indices_passive                   []
% 7.48/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.48/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.48  --sup_full_bw                           [BwDemod]
% 7.48/1.48  --sup_immed_triv                        [TrivRules]
% 7.48/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.48/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.48  --sup_immed_bw_main                     []
% 7.48/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.48/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.48/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.48/1.48  
% 7.48/1.48  ------ Combination Options
% 7.48/1.48  
% 7.48/1.48  --comb_res_mult                         3
% 7.48/1.48  --comb_sup_mult                         2
% 7.48/1.48  --comb_inst_mult                        10
% 7.48/1.48  
% 7.48/1.48  ------ Debug Options
% 7.48/1.48  
% 7.48/1.48  --dbg_backtrace                         false
% 7.48/1.48  --dbg_dump_prop_clauses                 false
% 7.48/1.48  --dbg_dump_prop_clauses_file            -
% 7.48/1.48  --dbg_out_stat                          false
% 7.48/1.48  ------ Parsing...
% 7.48/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.48/1.48  
% 7.48/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.48/1.48  
% 7.48/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.48/1.48  
% 7.48/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.48/1.48  ------ Proving...
% 7.48/1.48  ------ Problem Properties 
% 7.48/1.48  
% 7.48/1.48  
% 7.48/1.48  clauses                                 52
% 7.48/1.48  conjectures                             6
% 7.48/1.48  EPR                                     5
% 7.48/1.48  Horn                                    49
% 7.48/1.48  unary                                   14
% 7.48/1.48  binary                                  17
% 7.48/1.48  lits                                    134
% 7.48/1.48  lits eq                                 32
% 7.48/1.48  fd_pure                                 0
% 7.48/1.48  fd_pseudo                               0
% 7.48/1.48  fd_cond                                 4
% 7.48/1.48  fd_pseudo_cond                          1
% 7.48/1.48  AC symbols                              0
% 7.48/1.48  
% 7.48/1.48  ------ Schedule dynamic 5 is on 
% 7.48/1.48  
% 7.48/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.48/1.48  
% 7.48/1.48  
% 7.48/1.48  ------ 
% 7.48/1.48  Current options:
% 7.48/1.48  ------ 
% 7.48/1.48  
% 7.48/1.48  ------ Input Options
% 7.48/1.48  
% 7.48/1.48  --out_options                           all
% 7.48/1.48  --tptp_safe_out                         true
% 7.48/1.48  --problem_path                          ""
% 7.48/1.48  --include_path                          ""
% 7.48/1.48  --clausifier                            res/vclausify_rel
% 7.48/1.48  --clausifier_options                    --mode clausify
% 7.48/1.48  --stdin                                 false
% 7.48/1.48  --stats_out                             all
% 7.48/1.48  
% 7.48/1.48  ------ General Options
% 7.48/1.48  
% 7.48/1.48  --fof                                   false
% 7.48/1.48  --time_out_real                         305.
% 7.48/1.48  --time_out_virtual                      -1.
% 7.48/1.48  --symbol_type_check                     false
% 7.48/1.48  --clausify_out                          false
% 7.48/1.48  --sig_cnt_out                           false
% 7.48/1.48  --trig_cnt_out                          false
% 7.48/1.48  --trig_cnt_out_tolerance                1.
% 7.48/1.48  --trig_cnt_out_sk_spl                   false
% 7.48/1.48  --abstr_cl_out                          false
% 7.48/1.48  
% 7.48/1.48  ------ Global Options
% 7.48/1.48  
% 7.48/1.48  --schedule                              default
% 7.48/1.48  --add_important_lit                     false
% 7.48/1.48  --prop_solver_per_cl                    1000
% 7.48/1.48  --min_unsat_core                        false
% 7.48/1.48  --soft_assumptions                      false
% 7.48/1.48  --soft_lemma_size                       3
% 7.48/1.48  --prop_impl_unit_size                   0
% 7.48/1.48  --prop_impl_unit                        []
% 7.48/1.48  --share_sel_clauses                     true
% 7.48/1.48  --reset_solvers                         false
% 7.48/1.48  --bc_imp_inh                            [conj_cone]
% 7.48/1.48  --conj_cone_tolerance                   3.
% 7.48/1.48  --extra_neg_conj                        none
% 7.48/1.48  --large_theory_mode                     true
% 7.48/1.48  --prolific_symb_bound                   200
% 7.48/1.48  --lt_threshold                          2000
% 7.48/1.48  --clause_weak_htbl                      true
% 7.48/1.48  --gc_record_bc_elim                     false
% 7.48/1.48  
% 7.48/1.48  ------ Preprocessing Options
% 7.48/1.48  
% 7.48/1.48  --preprocessing_flag                    true
% 7.48/1.48  --time_out_prep_mult                    0.1
% 7.48/1.48  --splitting_mode                        input
% 7.48/1.48  --splitting_grd                         true
% 7.48/1.48  --splitting_cvd                         false
% 7.48/1.48  --splitting_cvd_svl                     false
% 7.48/1.48  --splitting_nvd                         32
% 7.48/1.48  --sub_typing                            true
% 7.48/1.48  --prep_gs_sim                           true
% 7.48/1.48  --prep_unflatten                        true
% 7.48/1.48  --prep_res_sim                          true
% 7.48/1.48  --prep_upred                            true
% 7.48/1.48  --prep_sem_filter                       exhaustive
% 7.48/1.48  --prep_sem_filter_out                   false
% 7.48/1.48  --pred_elim                             true
% 7.48/1.48  --res_sim_input                         true
% 7.48/1.48  --eq_ax_congr_red                       true
% 7.48/1.48  --pure_diseq_elim                       true
% 7.48/1.48  --brand_transform                       false
% 7.48/1.48  --non_eq_to_eq                          false
% 7.48/1.48  --prep_def_merge                        true
% 7.48/1.48  --prep_def_merge_prop_impl              false
% 7.48/1.48  --prep_def_merge_mbd                    true
% 7.48/1.48  --prep_def_merge_tr_red                 false
% 7.48/1.48  --prep_def_merge_tr_cl                  false
% 7.48/1.48  --smt_preprocessing                     true
% 7.48/1.48  --smt_ac_axioms                         fast
% 7.48/1.48  --preprocessed_out                      false
% 7.48/1.48  --preprocessed_stats                    false
% 7.48/1.48  
% 7.48/1.48  ------ Abstraction refinement Options
% 7.48/1.48  
% 7.48/1.48  --abstr_ref                             []
% 7.48/1.48  --abstr_ref_prep                        false
% 7.48/1.48  --abstr_ref_until_sat                   false
% 7.48/1.48  --abstr_ref_sig_restrict                funpre
% 7.48/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.48/1.48  --abstr_ref_under                       []
% 7.48/1.48  
% 7.48/1.48  ------ SAT Options
% 7.48/1.48  
% 7.48/1.48  --sat_mode                              false
% 7.48/1.48  --sat_fm_restart_options                ""
% 7.48/1.48  --sat_gr_def                            false
% 7.48/1.48  --sat_epr_types                         true
% 7.48/1.48  --sat_non_cyclic_types                  false
% 7.48/1.48  --sat_finite_models                     false
% 7.48/1.48  --sat_fm_lemmas                         false
% 7.48/1.48  --sat_fm_prep                           false
% 7.48/1.48  --sat_fm_uc_incr                        true
% 7.48/1.48  --sat_out_model                         small
% 7.48/1.48  --sat_out_clauses                       false
% 7.48/1.48  
% 7.48/1.48  ------ QBF Options
% 7.48/1.48  
% 7.48/1.48  --qbf_mode                              false
% 7.48/1.48  --qbf_elim_univ                         false
% 7.48/1.48  --qbf_dom_inst                          none
% 7.48/1.48  --qbf_dom_pre_inst                      false
% 7.48/1.48  --qbf_sk_in                             false
% 7.48/1.48  --qbf_pred_elim                         true
% 7.48/1.48  --qbf_split                             512
% 7.48/1.48  
% 7.48/1.48  ------ BMC1 Options
% 7.48/1.48  
% 7.48/1.48  --bmc1_incremental                      false
% 7.48/1.48  --bmc1_axioms                           reachable_all
% 7.48/1.48  --bmc1_min_bound                        0
% 7.48/1.48  --bmc1_max_bound                        -1
% 7.48/1.48  --bmc1_max_bound_default                -1
% 7.48/1.48  --bmc1_symbol_reachability              true
% 7.48/1.48  --bmc1_property_lemmas                  false
% 7.48/1.48  --bmc1_k_induction                      false
% 7.48/1.48  --bmc1_non_equiv_states                 false
% 7.48/1.48  --bmc1_deadlock                         false
% 7.48/1.48  --bmc1_ucm                              false
% 7.48/1.48  --bmc1_add_unsat_core                   none
% 7.48/1.48  --bmc1_unsat_core_children              false
% 7.48/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.48/1.48  --bmc1_out_stat                         full
% 7.48/1.48  --bmc1_ground_init                      false
% 7.48/1.48  --bmc1_pre_inst_next_state              false
% 7.48/1.48  --bmc1_pre_inst_state                   false
% 7.48/1.48  --bmc1_pre_inst_reach_state             false
% 7.48/1.48  --bmc1_out_unsat_core                   false
% 7.48/1.48  --bmc1_aig_witness_out                  false
% 7.48/1.48  --bmc1_verbose                          false
% 7.48/1.48  --bmc1_dump_clauses_tptp                false
% 7.48/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.48/1.48  --bmc1_dump_file                        -
% 7.48/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.48/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.48/1.48  --bmc1_ucm_extend_mode                  1
% 7.48/1.48  --bmc1_ucm_init_mode                    2
% 7.48/1.48  --bmc1_ucm_cone_mode                    none
% 7.48/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.48/1.48  --bmc1_ucm_relax_model                  4
% 7.48/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.48/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.48/1.48  --bmc1_ucm_layered_model                none
% 7.48/1.48  --bmc1_ucm_max_lemma_size               10
% 7.48/1.48  
% 7.48/1.48  ------ AIG Options
% 7.48/1.48  
% 7.48/1.48  --aig_mode                              false
% 7.48/1.48  
% 7.48/1.48  ------ Instantiation Options
% 7.48/1.48  
% 7.48/1.48  --instantiation_flag                    true
% 7.48/1.48  --inst_sos_flag                         false
% 7.48/1.48  --inst_sos_phase                        true
% 7.48/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.48/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.48/1.48  --inst_lit_sel_side                     none
% 7.48/1.48  --inst_solver_per_active                1400
% 7.48/1.48  --inst_solver_calls_frac                1.
% 7.48/1.48  --inst_passive_queue_type               priority_queues
% 7.48/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.48/1.48  --inst_passive_queues_freq              [25;2]
% 7.48/1.48  --inst_dismatching                      true
% 7.48/1.48  --inst_eager_unprocessed_to_passive     true
% 7.48/1.48  --inst_prop_sim_given                   true
% 7.48/1.48  --inst_prop_sim_new                     false
% 7.48/1.48  --inst_subs_new                         false
% 7.48/1.48  --inst_eq_res_simp                      false
% 7.48/1.48  --inst_subs_given                       false
% 7.48/1.48  --inst_orphan_elimination               true
% 7.48/1.48  --inst_learning_loop_flag               true
% 7.48/1.48  --inst_learning_start                   3000
% 7.48/1.48  --inst_learning_factor                  2
% 7.48/1.48  --inst_start_prop_sim_after_learn       3
% 7.48/1.48  --inst_sel_renew                        solver
% 7.48/1.48  --inst_lit_activity_flag                true
% 7.48/1.48  --inst_restr_to_given                   false
% 7.48/1.48  --inst_activity_threshold               500
% 7.48/1.48  --inst_out_proof                        true
% 7.48/1.48  
% 7.48/1.48  ------ Resolution Options
% 7.48/1.48  
% 7.48/1.48  --resolution_flag                       false
% 7.48/1.48  --res_lit_sel                           adaptive
% 7.48/1.48  --res_lit_sel_side                      none
% 7.48/1.48  --res_ordering                          kbo
% 7.48/1.48  --res_to_prop_solver                    active
% 7.48/1.48  --res_prop_simpl_new                    false
% 7.48/1.48  --res_prop_simpl_given                  true
% 7.48/1.48  --res_passive_queue_type                priority_queues
% 7.48/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.48/1.48  --res_passive_queues_freq               [15;5]
% 7.48/1.48  --res_forward_subs                      full
% 7.48/1.48  --res_backward_subs                     full
% 7.48/1.48  --res_forward_subs_resolution           true
% 7.48/1.48  --res_backward_subs_resolution          true
% 7.48/1.48  --res_orphan_elimination                true
% 7.48/1.48  --res_time_limit                        2.
% 7.48/1.48  --res_out_proof                         true
% 7.48/1.48  
% 7.48/1.48  ------ Superposition Options
% 7.48/1.48  
% 7.48/1.48  --superposition_flag                    true
% 7.48/1.48  --sup_passive_queue_type                priority_queues
% 7.48/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.48/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.48/1.48  --demod_completeness_check              fast
% 7.48/1.48  --demod_use_ground                      true
% 7.48/1.48  --sup_to_prop_solver                    passive
% 7.48/1.48  --sup_prop_simpl_new                    true
% 7.48/1.48  --sup_prop_simpl_given                  true
% 7.48/1.48  --sup_fun_splitting                     false
% 7.48/1.48  --sup_smt_interval                      50000
% 7.48/1.48  
% 7.48/1.48  ------ Superposition Simplification Setup
% 7.48/1.48  
% 7.48/1.48  --sup_indices_passive                   []
% 7.48/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.48/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.48/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.48  --sup_full_bw                           [BwDemod]
% 7.48/1.48  --sup_immed_triv                        [TrivRules]
% 7.48/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.48/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.48  --sup_immed_bw_main                     []
% 7.48/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.48/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.48/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.48/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.48/1.48  
% 7.48/1.48  ------ Combination Options
% 7.48/1.48  
% 7.48/1.48  --comb_res_mult                         3
% 7.48/1.48  --comb_sup_mult                         2
% 7.48/1.48  --comb_inst_mult                        10
% 7.48/1.48  
% 7.48/1.48  ------ Debug Options
% 7.48/1.48  
% 7.48/1.48  --dbg_backtrace                         false
% 7.48/1.48  --dbg_dump_prop_clauses                 false
% 7.48/1.48  --dbg_dump_prop_clauses_file            -
% 7.48/1.48  --dbg_out_stat                          false
% 7.48/1.48  
% 7.48/1.48  
% 7.48/1.48  
% 7.48/1.48  
% 7.48/1.48  ------ Proving...
% 7.48/1.48  
% 7.48/1.48  
% 7.48/1.48  % SZS status Theorem for theBenchmark.p
% 7.48/1.48  
% 7.48/1.48   Resolution empty clause
% 7.48/1.48  
% 7.48/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.48/1.48  
% 7.48/1.48  fof(f36,conjecture,(
% 7.48/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f37,negated_conjecture,(
% 7.48/1.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.48/1.48    inference(negated_conjecture,[],[f36])).
% 7.48/1.48  
% 7.48/1.48  fof(f75,plain,(
% 7.48/1.48    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.48/1.48    inference(ennf_transformation,[],[f37])).
% 7.48/1.48  
% 7.48/1.48  fof(f76,plain,(
% 7.48/1.48    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.48/1.48    inference(flattening,[],[f75])).
% 7.48/1.48  
% 7.48/1.48  fof(f84,plain,(
% 7.48/1.48    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 7.48/1.48    introduced(choice_axiom,[])).
% 7.48/1.48  
% 7.48/1.48  fof(f85,plain,(
% 7.48/1.48    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 7.48/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f76,f84])).
% 7.48/1.48  
% 7.48/1.48  fof(f144,plain,(
% 7.48/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.48/1.48    inference(cnf_transformation,[],[f85])).
% 7.48/1.48  
% 7.48/1.48  fof(f5,axiom,(
% 7.48/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f81,plain,(
% 7.48/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.48/1.48    inference(nnf_transformation,[],[f5])).
% 7.48/1.48  
% 7.48/1.48  fof(f92,plain,(
% 7.48/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.48/1.48    inference(cnf_transformation,[],[f81])).
% 7.48/1.48  
% 7.48/1.48  fof(f32,axiom,(
% 7.48/1.48    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f131,plain,(
% 7.48/1.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.48/1.48    inference(cnf_transformation,[],[f32])).
% 7.48/1.48  
% 7.48/1.48  fof(f35,axiom,(
% 7.48/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f73,plain,(
% 7.48/1.48    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.48/1.48    inference(ennf_transformation,[],[f35])).
% 7.48/1.48  
% 7.48/1.48  fof(f74,plain,(
% 7.48/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.48/1.48    inference(flattening,[],[f73])).
% 7.48/1.48  
% 7.48/1.48  fof(f140,plain,(
% 7.48/1.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f74])).
% 7.48/1.48  
% 7.48/1.48  fof(f21,axiom,(
% 7.48/1.48    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f116,plain,(
% 7.48/1.48    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 7.48/1.48    inference(cnf_transformation,[],[f21])).
% 7.48/1.48  
% 7.48/1.48  fof(f33,axiom,(
% 7.48/1.48    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f132,plain,(
% 7.48/1.48    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f33])).
% 7.48/1.48  
% 7.48/1.48  fof(f152,plain,(
% 7.48/1.48    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 7.48/1.48    inference(definition_unfolding,[],[f116,f132])).
% 7.48/1.48  
% 7.48/1.48  fof(f31,axiom,(
% 7.48/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f69,plain,(
% 7.48/1.48    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.48/1.48    inference(ennf_transformation,[],[f31])).
% 7.48/1.48  
% 7.48/1.48  fof(f70,plain,(
% 7.48/1.48    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.48/1.48    inference(flattening,[],[f69])).
% 7.48/1.48  
% 7.48/1.48  fof(f129,plain,(
% 7.48/1.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.48/1.48    inference(cnf_transformation,[],[f70])).
% 7.48/1.48  
% 7.48/1.48  fof(f130,plain,(
% 7.48/1.48    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f32])).
% 7.48/1.48  
% 7.48/1.48  fof(f30,axiom,(
% 7.48/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f68,plain,(
% 7.48/1.48    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.48/1.48    inference(ennf_transformation,[],[f30])).
% 7.48/1.48  
% 7.48/1.48  fof(f127,plain,(
% 7.48/1.48    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.48/1.48    inference(cnf_transformation,[],[f68])).
% 7.48/1.48  
% 7.48/1.48  fof(f15,axiom,(
% 7.48/1.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f108,plain,(
% 7.48/1.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.48/1.48    inference(cnf_transformation,[],[f15])).
% 7.48/1.48  
% 7.48/1.48  fof(f148,plain,(
% 7.48/1.48    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 7.48/1.48    inference(definition_unfolding,[],[f108,f132])).
% 7.48/1.48  
% 7.48/1.48  fof(f28,axiom,(
% 7.48/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f66,plain,(
% 7.48/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.48/1.48    inference(ennf_transformation,[],[f28])).
% 7.48/1.48  
% 7.48/1.48  fof(f125,plain,(
% 7.48/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.48/1.48    inference(cnf_transformation,[],[f66])).
% 7.48/1.48  
% 7.48/1.48  fof(f29,axiom,(
% 7.48/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f38,plain,(
% 7.48/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.48/1.48    inference(pure_predicate_removal,[],[f29])).
% 7.48/1.48  
% 7.48/1.48  fof(f67,plain,(
% 7.48/1.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.48/1.48    inference(ennf_transformation,[],[f38])).
% 7.48/1.48  
% 7.48/1.48  fof(f126,plain,(
% 7.48/1.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.48/1.48    inference(cnf_transformation,[],[f67])).
% 7.48/1.48  
% 7.48/1.48  fof(f7,axiom,(
% 7.48/1.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f41,plain,(
% 7.48/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.48/1.48    inference(ennf_transformation,[],[f7])).
% 7.48/1.48  
% 7.48/1.48  fof(f82,plain,(
% 7.48/1.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.48/1.48    inference(nnf_transformation,[],[f41])).
% 7.48/1.48  
% 7.48/1.48  fof(f95,plain,(
% 7.48/1.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f82])).
% 7.48/1.48  
% 7.48/1.48  fof(f8,axiom,(
% 7.48/1.48    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f42,plain,(
% 7.48/1.48    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.48/1.48    inference(ennf_transformation,[],[f8])).
% 7.48/1.48  
% 7.48/1.48  fof(f97,plain,(
% 7.48/1.48    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f42])).
% 7.48/1.48  
% 7.48/1.48  fof(f146,plain,(
% 7.48/1.48    k2_relset_1(sK1,sK2,sK3) = sK2),
% 7.48/1.48    inference(cnf_transformation,[],[f85])).
% 7.48/1.48  
% 7.48/1.48  fof(f13,axiom,(
% 7.48/1.48    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f47,plain,(
% 7.48/1.48    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.48/1.48    inference(ennf_transformation,[],[f13])).
% 7.48/1.48  
% 7.48/1.48  fof(f48,plain,(
% 7.48/1.48    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.48/1.48    inference(flattening,[],[f47])).
% 7.48/1.48  
% 7.48/1.48  fof(f104,plain,(
% 7.48/1.48    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f48])).
% 7.48/1.48  
% 7.48/1.48  fof(f12,axiom,(
% 7.48/1.48    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f46,plain,(
% 7.48/1.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.48/1.48    inference(ennf_transformation,[],[f12])).
% 7.48/1.48  
% 7.48/1.48  fof(f102,plain,(
% 7.48/1.48    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f46])).
% 7.48/1.48  
% 7.48/1.48  fof(f34,axiom,(
% 7.48/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f71,plain,(
% 7.48/1.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.48/1.48    inference(ennf_transformation,[],[f34])).
% 7.48/1.48  
% 7.48/1.48  fof(f72,plain,(
% 7.48/1.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.48/1.48    inference(flattening,[],[f71])).
% 7.48/1.48  
% 7.48/1.48  fof(f135,plain,(
% 7.48/1.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f72])).
% 7.48/1.48  
% 7.48/1.48  fof(f101,plain,(
% 7.48/1.48    ( ! [X0] : (k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f46])).
% 7.48/1.48  
% 7.48/1.48  fof(f142,plain,(
% 7.48/1.48    v1_funct_1(sK3)),
% 7.48/1.48    inference(cnf_transformation,[],[f85])).
% 7.48/1.48  
% 7.48/1.48  fof(f19,axiom,(
% 7.48/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f52,plain,(
% 7.48/1.48    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.48/1.48    inference(ennf_transformation,[],[f19])).
% 7.48/1.48  
% 7.48/1.48  fof(f53,plain,(
% 7.48/1.48    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.48/1.48    inference(flattening,[],[f52])).
% 7.48/1.48  
% 7.48/1.48  fof(f112,plain,(
% 7.48/1.48    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f53])).
% 7.48/1.48  
% 7.48/1.48  fof(f145,plain,(
% 7.48/1.48    v2_funct_1(sK3)),
% 7.48/1.48    inference(cnf_transformation,[],[f85])).
% 7.48/1.48  
% 7.48/1.48  fof(f20,axiom,(
% 7.48/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f54,plain,(
% 7.48/1.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.48/1.48    inference(ennf_transformation,[],[f20])).
% 7.48/1.48  
% 7.48/1.48  fof(f55,plain,(
% 7.48/1.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.48/1.48    inference(flattening,[],[f54])).
% 7.48/1.48  
% 7.48/1.48  fof(f114,plain,(
% 7.48/1.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f55])).
% 7.48/1.48  
% 7.48/1.48  fof(f14,axiom,(
% 7.48/1.48    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f49,plain,(
% 7.48/1.48    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.48/1.48    inference(ennf_transformation,[],[f14])).
% 7.48/1.48  
% 7.48/1.48  fof(f83,plain,(
% 7.48/1.48    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.48/1.48    inference(nnf_transformation,[],[f49])).
% 7.48/1.48  
% 7.48/1.48  fof(f105,plain,(
% 7.48/1.48    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f83])).
% 7.48/1.48  
% 7.48/1.48  fof(f138,plain,(
% 7.48/1.48    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f74])).
% 7.48/1.48  
% 7.48/1.48  fof(f134,plain,(
% 7.48/1.48    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f72])).
% 7.48/1.48  
% 7.48/1.48  fof(f147,plain,(
% 7.48/1.48    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 7.48/1.48    inference(cnf_transformation,[],[f85])).
% 7.48/1.48  
% 7.48/1.48  fof(f93,plain,(
% 7.48/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f81])).
% 7.48/1.48  
% 7.48/1.48  fof(f107,plain,(
% 7.48/1.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.48/1.48    inference(cnf_transformation,[],[f15])).
% 7.48/1.48  
% 7.48/1.48  fof(f149,plain,(
% 7.48/1.48    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 7.48/1.48    inference(definition_unfolding,[],[f107,f132])).
% 7.48/1.48  
% 7.48/1.48  fof(f1,axiom,(
% 7.48/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f39,plain,(
% 7.48/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.48/1.48    inference(ennf_transformation,[],[f1])).
% 7.48/1.48  
% 7.48/1.48  fof(f77,plain,(
% 7.48/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.48/1.48    inference(nnf_transformation,[],[f39])).
% 7.48/1.48  
% 7.48/1.48  fof(f78,plain,(
% 7.48/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.48/1.48    inference(rectify,[],[f77])).
% 7.48/1.48  
% 7.48/1.48  fof(f79,plain,(
% 7.48/1.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.48/1.48    introduced(choice_axiom,[])).
% 7.48/1.48  
% 7.48/1.48  fof(f80,plain,(
% 7.48/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.48/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f78,f79])).
% 7.48/1.48  
% 7.48/1.48  fof(f87,plain,(
% 7.48/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f80])).
% 7.48/1.48  
% 7.48/1.48  fof(f2,axiom,(
% 7.48/1.48    v1_xboole_0(k1_xboole_0)),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f89,plain,(
% 7.48/1.48    v1_xboole_0(k1_xboole_0)),
% 7.48/1.48    inference(cnf_transformation,[],[f2])).
% 7.48/1.48  
% 7.48/1.48  fof(f6,axiom,(
% 7.48/1.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f40,plain,(
% 7.48/1.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.48/1.48    inference(ennf_transformation,[],[f6])).
% 7.48/1.48  
% 7.48/1.48  fof(f94,plain,(
% 7.48/1.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f40])).
% 7.48/1.48  
% 7.48/1.48  fof(f17,axiom,(
% 7.48/1.48    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f110,plain,(
% 7.48/1.48    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 7.48/1.48    inference(cnf_transformation,[],[f17])).
% 7.48/1.48  
% 7.48/1.48  fof(f151,plain,(
% 7.48/1.48    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 7.48/1.48    inference(definition_unfolding,[],[f110,f132])).
% 7.48/1.48  
% 7.48/1.48  fof(f22,axiom,(
% 7.48/1.48    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.48/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.48/1.48  
% 7.48/1.48  fof(f117,plain,(
% 7.48/1.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.48/1.48    inference(cnf_transformation,[],[f22])).
% 7.48/1.48  
% 7.48/1.48  fof(f155,plain,(
% 7.48/1.48    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 7.48/1.48    inference(definition_unfolding,[],[f117,f132])).
% 7.48/1.48  
% 7.48/1.48  fof(f103,plain,(
% 7.48/1.48    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f48])).
% 7.48/1.48  
% 7.48/1.48  fof(f139,plain,(
% 7.48/1.48    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 != X0 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.48/1.48    inference(cnf_transformation,[],[f74])).
% 7.48/1.48  
% 7.48/1.48  fof(f159,plain,(
% 7.48/1.48    ( ! [X2,X3,X1] : (v1_funct_2(X3,k1_xboole_0,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3)) )),
% 7.48/1.48    inference(equality_resolution,[],[f139])).
% 7.48/1.48  
% 7.48/1.48  cnf(c_58,negated_conjecture,
% 7.48/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.48/1.48      inference(cnf_transformation,[],[f144]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4205,plain,
% 7.48/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_7,plain,
% 7.48/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.48/1.48      inference(cnf_transformation,[],[f92]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4240,plain,
% 7.48/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.48/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_6406,plain,
% 7.48/1.48      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_4205,c_4240]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_44,plain,
% 7.48/1.48      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.48/1.48      inference(cnf_transformation,[],[f131]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4214,plain,
% 7.48/1.48      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_50,plain,
% 7.48/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.48/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.48/1.48      | ~ r1_tarski(X2,X3)
% 7.48/1.48      | ~ v1_funct_1(X0)
% 7.48/1.48      | k1_xboole_0 = X2 ),
% 7.48/1.48      inference(cnf_transformation,[],[f140]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4210,plain,
% 7.48/1.48      ( k1_xboole_0 = X0
% 7.48/1.48      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.48/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.48/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 7.48/1.48      | r1_tarski(X0,X3) != iProver_top
% 7.48/1.48      | v1_funct_1(X1) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_7758,plain,
% 7.48/1.48      ( k1_xboole_0 = X0
% 7.48/1.48      | v1_funct_2(k6_partfun1(X0),X0,X0) != iProver_top
% 7.48/1.48      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 7.48/1.48      | r1_tarski(X0,X1) != iProver_top
% 7.48/1.48      | v1_funct_1(k6_partfun1(X0)) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_4214,c_4210]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29,plain,
% 7.48/1.48      ( v1_funct_1(k6_partfun1(X0)) ),
% 7.48/1.48      inference(cnf_transformation,[],[f152]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_123,plain,
% 7.48/1.48      ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_42,plain,
% 7.48/1.48      ( v1_funct_2(X0,X1,X2)
% 7.48/1.48      | ~ v1_partfun1(X0,X1)
% 7.48/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.48      | ~ v1_funct_1(X0) ),
% 7.48/1.48      inference(cnf_transformation,[],[f129]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_45,plain,
% 7.48/1.48      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 7.48/1.48      inference(cnf_transformation,[],[f130]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_718,plain,
% 7.48/1.48      ( v1_funct_2(X0,X1,X2)
% 7.48/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.48      | ~ v1_funct_1(X0)
% 7.48/1.48      | X3 != X1
% 7.48/1.48      | k6_partfun1(X3) != X0 ),
% 7.48/1.48      inference(resolution_lifted,[status(thm)],[c_42,c_45]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_719,plain,
% 7.48/1.48      ( v1_funct_2(k6_partfun1(X0),X0,X1)
% 7.48/1.48      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.48/1.48      | ~ v1_funct_1(k6_partfun1(X0)) ),
% 7.48/1.48      inference(unflattening,[status(thm)],[c_718]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_723,plain,
% 7.48/1.48      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.48/1.48      | v1_funct_2(k6_partfun1(X0),X0,X1) ),
% 7.48/1.48      inference(global_propositional_subsumption,[status(thm)],[c_719,c_29]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_724,plain,
% 7.48/1.48      ( v1_funct_2(k6_partfun1(X0),X0,X1)
% 7.48/1.48      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.48/1.48      inference(renaming,[status(thm)],[c_723]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4200,plain,
% 7.48/1.48      ( v1_funct_2(k6_partfun1(X0),X0,X1) = iProver_top
% 7.48/1.48      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_724]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_5540,plain,
% 7.48/1.48      ( v1_funct_2(k6_partfun1(X0),X0,X0) = iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_4214,c_4200]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29255,plain,
% 7.48/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.48/1.48      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 7.48/1.48      | k1_xboole_0 = X0 ),
% 7.48/1.48      inference(global_propositional_subsumption,
% 7.48/1.48                [status(thm)],
% 7.48/1.48                [c_7758,c_123,c_5540]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29256,plain,
% 7.48/1.48      ( k1_xboole_0 = X0
% 7.48/1.48      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 7.48/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.48/1.48      inference(renaming,[status(thm)],[c_29255]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_41,plain,
% 7.48/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.48      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.48/1.48      inference(cnf_transformation,[],[f127]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4215,plain,
% 7.48/1.48      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.48/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29268,plain,
% 7.48/1.48      ( k2_relset_1(X0,X1,k6_partfun1(X0)) = k2_relat_1(k6_partfun1(X0))
% 7.48/1.48      | k1_xboole_0 = X0
% 7.48/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_29256,c_4215]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_21,plain,
% 7.48/1.48      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 7.48/1.48      inference(cnf_transformation,[],[f148]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29303,plain,
% 7.48/1.48      ( k2_relset_1(X0,X1,k6_partfun1(X0)) = X0
% 7.48/1.48      | k1_xboole_0 = X0
% 7.48/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.48/1.48      inference(light_normalisation,[status(thm)],[c_29268,c_21]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29326,plain,
% 7.48/1.48      ( k2_relset_1(sK3,k2_zfmisc_1(sK1,sK2),k6_partfun1(sK3)) = sK3
% 7.48/1.48      | sK3 = k1_xboole_0 ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_6406,c_29303]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_63,plain,
% 7.48/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_39,plain,
% 7.48/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.48/1.48      inference(cnf_transformation,[],[f125]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4704,plain,
% 7.48/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.48/1.48      | v1_relat_1(sK3) ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_39]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4705,plain,
% 7.48/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.48/1.48      | v1_relat_1(sK3) = iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_4704]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_40,plain,
% 7.48/1.48      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.48/1.48      inference(cnf_transformation,[],[f126]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_10,plain,
% 7.48/1.48      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.48/1.48      inference(cnf_transformation,[],[f95]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_739,plain,
% 7.48/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.48      | r1_tarski(k1_relat_1(X0),X1)
% 7.48/1.48      | ~ v1_relat_1(X0) ),
% 7.48/1.48      inference(resolution,[status(thm)],[c_40,c_10]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_743,plain,
% 7.48/1.48      ( r1_tarski(k1_relat_1(X0),X1)
% 7.48/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.48/1.48      inference(global_propositional_subsumption,[status(thm)],[c_739,c_39]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_744,plain,
% 7.48/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.48      | r1_tarski(k1_relat_1(X0),X1) ),
% 7.48/1.48      inference(renaming,[status(thm)],[c_743]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4781,plain,
% 7.48/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.48/1.48      | r1_tarski(k1_relat_1(sK3),sK1) ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_744]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4782,plain,
% 7.48/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.48/1.48      | r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_4781]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_11,plain,
% 7.48/1.48      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 7.48/1.48      inference(cnf_transformation,[],[f97]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4915,plain,
% 7.48/1.48      ( v1_relat_1(k4_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_11]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4928,plain,
% 7.48/1.48      ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
% 7.48/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_4915]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_5447,plain,
% 7.48/1.48      ( v1_relat_1(k4_relat_1(k4_relat_1(sK3)))
% 7.48/1.48      | ~ v1_relat_1(k4_relat_1(sK3)) ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_11]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_5460,plain,
% 7.48/1.48      ( v1_relat_1(k4_relat_1(k4_relat_1(sK3))) = iProver_top
% 7.48/1.48      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_5447]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_9199,plain,
% 7.48/1.48      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_4205,c_4215]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_56,negated_conjecture,
% 7.48/1.48      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 7.48/1.48      inference(cnf_transformation,[],[f146]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_9233,plain,
% 7.48/1.48      ( k2_relat_1(sK3) = sK2 ),
% 7.48/1.48      inference(light_normalisation,[status(thm)],[c_9199,c_56]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_17,plain,
% 7.48/1.48      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 7.48/1.48      inference(cnf_transformation,[],[f104]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4233,plain,
% 7.48/1.48      ( k2_relat_1(X0) != k1_xboole_0
% 7.48/1.48      | k1_xboole_0 = X0
% 7.48/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_9291,plain,
% 7.48/1.48      ( sK2 != k1_xboole_0
% 7.48/1.48      | sK3 = k1_xboole_0
% 7.48/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_9233,c_4233]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_9439,plain,
% 7.48/1.48      ( sK3 = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 7.48/1.48      inference(global_propositional_subsumption,
% 7.48/1.48                [status(thm)],
% 7.48/1.48                [c_9291,c_63,c_4705]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_9440,plain,
% 7.48/1.48      ( sK2 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 7.48/1.48      inference(renaming,[status(thm)],[c_9439]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4216,plain,
% 7.48/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.48/1.48      | v1_relat_1(X0) = iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_6743,plain,
% 7.48/1.48      ( v1_relat_1(sK3) = iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_4205,c_4216]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_15,plain,
% 7.48/1.48      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 7.48/1.48      inference(cnf_transformation,[],[f102]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4235,plain,
% 7.48/1.48      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 7.48/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_7174,plain,
% 7.48/1.48      ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_6743,c_4235]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_46,plain,
% 7.48/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.48/1.48      | ~ v1_funct_1(X0)
% 7.48/1.48      | ~ v1_relat_1(X0) ),
% 7.48/1.48      inference(cnf_transformation,[],[f135]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4213,plain,
% 7.48/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 7.48/1.48      | v1_funct_1(X0) != iProver_top
% 7.48/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_10174,plain,
% 7.48/1.48      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 7.48/1.48      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 7.48/1.48      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_7174,c_4213]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_16,plain,
% 7.48/1.48      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 7.48/1.48      inference(cnf_transformation,[],[f101]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4234,plain,
% 7.48/1.48      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 7.48/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_7175,plain,
% 7.48/1.48      ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_6743,c_4234]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_9281,plain,
% 7.48/1.48      ( k1_relat_1(k4_relat_1(sK3)) = sK2 ),
% 7.48/1.48      inference(demodulation,[status(thm)],[c_9233,c_7175]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_10223,plain,
% 7.48/1.48      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 7.48/1.48      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 7.48/1.48      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 7.48/1.48      inference(light_normalisation,[status(thm)],[c_10174,c_9281]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_60,negated_conjecture,
% 7.48/1.48      ( v1_funct_1(sK3) ),
% 7.48/1.48      inference(cnf_transformation,[],[f142]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_61,plain,
% 7.48/1.48      ( v1_funct_1(sK3) = iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4203,plain,
% 7.48/1.48      ( v1_funct_1(sK3) = iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_26,plain,
% 7.48/1.48      ( ~ v1_funct_1(X0)
% 7.48/1.48      | ~ v2_funct_1(X0)
% 7.48/1.48      | ~ v1_relat_1(X0)
% 7.48/1.48      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 7.48/1.48      inference(cnf_transformation,[],[f112]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4227,plain,
% 7.48/1.48      ( k2_funct_1(X0) = k4_relat_1(X0)
% 7.48/1.48      | v1_funct_1(X0) != iProver_top
% 7.48/1.48      | v2_funct_1(X0) != iProver_top
% 7.48/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_11522,plain,
% 7.48/1.48      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 7.48/1.48      | v2_funct_1(sK3) != iProver_top
% 7.48/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_4203,c_4227]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_57,negated_conjecture,
% 7.48/1.48      ( v2_funct_1(sK3) ),
% 7.48/1.48      inference(cnf_transformation,[],[f145]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_917,plain,
% 7.48/1.48      ( ~ v1_funct_1(X0)
% 7.48/1.48      | ~ v1_relat_1(X0)
% 7.48/1.48      | k2_funct_1(X0) = k4_relat_1(X0)
% 7.48/1.48      | sK3 != X0 ),
% 7.48/1.48      inference(resolution_lifted,[status(thm)],[c_26,c_57]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_918,plain,
% 7.48/1.48      ( ~ v1_funct_1(sK3)
% 7.48/1.48      | ~ v1_relat_1(sK3)
% 7.48/1.48      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 7.48/1.48      inference(unflattening,[status(thm)],[c_917]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_11889,plain,
% 7.48/1.48      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 7.48/1.48      inference(global_propositional_subsumption,
% 7.48/1.48                [status(thm)],
% 7.48/1.48                [c_11522,c_60,c_58,c_918,c_4704]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_27,plain,
% 7.48/1.48      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 7.48/1.48      inference(cnf_transformation,[],[f114]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4226,plain,
% 7.48/1.48      ( v1_funct_1(X0) != iProver_top
% 7.48/1.48      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 7.48/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_11907,plain,
% 7.48/1.48      ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
% 7.48/1.48      | v1_funct_1(sK3) != iProver_top
% 7.48/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_11889,c_4226]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_14814,plain,
% 7.48/1.48      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 7.48/1.48      inference(global_propositional_subsumption,
% 7.48/1.48                [status(thm)],
% 7.48/1.48                [c_10223,c_61,c_63,c_4705,c_4928,c_11907]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_14820,plain,
% 7.48/1.48      ( v1_relat_1(k4_relat_1(sK3)) = iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_14814,c_4216]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_15322,plain,
% 7.48/1.48      ( k1_relat_1(k4_relat_1(k4_relat_1(sK3))) = k2_relat_1(k4_relat_1(sK3)) ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_14820,c_4234]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_15328,plain,
% 7.48/1.48      ( k1_relat_1(k4_relat_1(k4_relat_1(sK3))) = k1_relat_1(sK3) ),
% 7.48/1.48      inference(light_normalisation,[status(thm)],[c_15322,c_7174]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_20,plain,
% 7.48/1.48      ( ~ v1_relat_1(X0)
% 7.48/1.48      | k2_relat_1(X0) = k1_xboole_0
% 7.48/1.48      | k1_relat_1(X0) != k1_xboole_0 ),
% 7.48/1.48      inference(cnf_transformation,[],[f105]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4230,plain,
% 7.48/1.48      ( k2_relat_1(X0) = k1_xboole_0
% 7.48/1.48      | k1_relat_1(X0) != k1_xboole_0
% 7.48/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_15697,plain,
% 7.48/1.48      ( k2_relat_1(k4_relat_1(k4_relat_1(sK3))) = k1_xboole_0
% 7.48/1.48      | k1_relat_1(sK3) != k1_xboole_0
% 7.48/1.48      | v1_relat_1(k4_relat_1(k4_relat_1(sK3))) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_15328,c_4230]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_15321,plain,
% 7.48/1.48      ( k2_relat_1(k4_relat_1(k4_relat_1(sK3))) = k1_relat_1(k4_relat_1(sK3)) ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_14820,c_4235]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_15331,plain,
% 7.48/1.48      ( k2_relat_1(k4_relat_1(k4_relat_1(sK3))) = sK2 ),
% 7.48/1.48      inference(light_normalisation,[status(thm)],[c_15321,c_9281]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_15708,plain,
% 7.48/1.48      ( k1_relat_1(sK3) != k1_xboole_0
% 7.48/1.48      | sK2 = k1_xboole_0
% 7.48/1.48      | v1_relat_1(k4_relat_1(k4_relat_1(sK3))) != iProver_top ),
% 7.48/1.48      inference(demodulation,[status(thm)],[c_15697,c_15331]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_52,plain,
% 7.48/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.48/1.48      | v1_funct_2(X0,X1,X3)
% 7.48/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.48/1.48      | ~ r1_tarski(X2,X3)
% 7.48/1.48      | ~ v1_funct_1(X0)
% 7.48/1.48      | k1_xboole_0 = X2 ),
% 7.48/1.48      inference(cnf_transformation,[],[f138]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4208,plain,
% 7.48/1.48      ( k1_xboole_0 = X0
% 7.48/1.48      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.48/1.48      | v1_funct_2(X1,X2,X3) = iProver_top
% 7.48/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.48/1.48      | r1_tarski(X0,X3) != iProver_top
% 7.48/1.48      | v1_funct_1(X1) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_14824,plain,
% 7.48/1.48      ( k1_relat_1(sK3) = k1_xboole_0
% 7.48/1.48      | v1_funct_2(k4_relat_1(sK3),sK2,X0) = iProver_top
% 7.48/1.48      | v1_funct_2(k4_relat_1(sK3),sK2,k1_relat_1(sK3)) != iProver_top
% 7.48/1.48      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.48/1.48      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_14814,c_4208]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_47,plain,
% 7.48/1.48      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 7.48/1.48      | ~ v1_funct_1(X0)
% 7.48/1.48      | ~ v1_relat_1(X0) ),
% 7.48/1.48      inference(cnf_transformation,[],[f134]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4212,plain,
% 7.48/1.48      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 7.48/1.48      | v1_funct_1(X0) != iProver_top
% 7.48/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_9729,plain,
% 7.48/1.48      ( v1_funct_2(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3)),k1_relat_1(sK3)) = iProver_top
% 7.48/1.48      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 7.48/1.48      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_7174,c_4212]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_9733,plain,
% 7.48/1.48      ( v1_funct_2(k4_relat_1(sK3),sK2,k1_relat_1(sK3)) = iProver_top
% 7.48/1.48      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 7.48/1.48      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 7.48/1.48      inference(light_normalisation,[status(thm)],[c_9729,c_9281]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29048,plain,
% 7.48/1.48      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.48/1.48      | k1_relat_1(sK3) = k1_xboole_0
% 7.48/1.48      | v1_funct_2(k4_relat_1(sK3),sK2,X0) = iProver_top ),
% 7.48/1.48      inference(global_propositional_subsumption,
% 7.48/1.48                [status(thm)],
% 7.48/1.48                [c_14824,c_61,c_63,c_4705,c_4928,c_9733,c_11907]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29049,plain,
% 7.48/1.48      ( k1_relat_1(sK3) = k1_xboole_0
% 7.48/1.48      | v1_funct_2(k4_relat_1(sK3),sK2,X0) = iProver_top
% 7.48/1.48      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.48/1.48      inference(renaming,[status(thm)],[c_29048]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_14823,plain,
% 7.48/1.48      ( k1_relat_1(sK3) = k1_xboole_0
% 7.48/1.48      | v1_funct_2(k4_relat_1(sK3),sK2,k1_relat_1(sK3)) != iProver_top
% 7.48/1.48      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.48/1.48      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.48/1.48      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_14814,c_4210]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29168,plain,
% 7.48/1.48      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.48/1.48      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.48/1.48      | k1_relat_1(sK3) = k1_xboole_0 ),
% 7.48/1.48      inference(global_propositional_subsumption,
% 7.48/1.48                [status(thm)],
% 7.48/1.48                [c_14823,c_61,c_63,c_4705,c_4928,c_9733,c_11907]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29169,plain,
% 7.48/1.48      ( k1_relat_1(sK3) = k1_xboole_0
% 7.48/1.48      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 7.48/1.48      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.48/1.48      inference(renaming,[status(thm)],[c_29168]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_55,negated_conjecture,
% 7.48/1.48      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 7.48/1.48      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.48/1.48      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 7.48/1.48      inference(cnf_transformation,[],[f147]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4207,plain,
% 7.48/1.48      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 7.48/1.48      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.48/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_11894,plain,
% 7.48/1.48      ( v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top
% 7.48/1.48      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.48/1.48      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 7.48/1.48      inference(demodulation,[status(thm)],[c_11889,c_4207]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_11924,plain,
% 7.48/1.48      ( m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.48/1.48      | v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top ),
% 7.48/1.48      inference(global_propositional_subsumption,
% 7.48/1.48                [status(thm)],
% 7.48/1.48                [c_11894,c_61,c_63,c_4705,c_11907]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_11925,plain,
% 7.48/1.48      ( v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top
% 7.48/1.48      | m1_subset_1(k4_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.48/1.48      inference(renaming,[status(thm)],[c_11924]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29183,plain,
% 7.48/1.48      ( k1_relat_1(sK3) = k1_xboole_0
% 7.48/1.48      | v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top
% 7.48/1.48      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_29169,c_11925]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29246,plain,
% 7.48/1.48      ( v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top
% 7.48/1.48      | k1_relat_1(sK3) = k1_xboole_0 ),
% 7.48/1.48      inference(global_propositional_subsumption,
% 7.48/1.48                [status(thm)],
% 7.48/1.48                [c_29183,c_63,c_4782]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29247,plain,
% 7.48/1.48      ( k1_relat_1(sK3) = k1_xboole_0
% 7.48/1.48      | v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top ),
% 7.48/1.48      inference(renaming,[status(thm)],[c_29246]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29252,plain,
% 7.48/1.48      ( k1_relat_1(sK3) = k1_xboole_0
% 7.48/1.48      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_29049,c_29247]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29414,plain,
% 7.48/1.48      ( sK3 = k1_xboole_0 ),
% 7.48/1.48      inference(global_propositional_subsumption,
% 7.48/1.48                [status(thm)],
% 7.48/1.48                [c_29326,c_63,c_4705,c_4782,c_4928,c_5460,c_9440,c_15708,
% 7.48/1.48                 c_29252]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_6,plain,
% 7.48/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.48/1.48      inference(cnf_transformation,[],[f93]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4241,plain,
% 7.48/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.48/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_6431,plain,
% 7.48/1.48      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 7.48/1.48      | r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,sK1)) != iProver_top
% 7.48/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_4241,c_4207]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4630,plain,
% 7.48/1.48      ( v1_funct_1(k2_funct_1(sK3)) | ~ v1_funct_1(sK3) | ~ v1_relat_1(sK3) ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_27]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4631,plain,
% 7.48/1.48      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 7.48/1.48      | v1_funct_1(sK3) != iProver_top
% 7.48/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_4630]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_6522,plain,
% 7.48/1.48      ( r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,sK1)) != iProver_top
% 7.48/1.48      | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
% 7.48/1.48      inference(global_propositional_subsumption,
% 7.48/1.48                [status(thm)],
% 7.48/1.48                [c_6431,c_61,c_63,c_4631,c_4705]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_6523,plain,
% 7.48/1.48      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 7.48/1.48      | r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,sK1)) != iProver_top ),
% 7.48/1.48      inference(renaming,[status(thm)],[c_6522]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_11893,plain,
% 7.48/1.48      ( v1_funct_2(k4_relat_1(sK3),sK2,sK1) != iProver_top
% 7.48/1.48      | r1_tarski(k4_relat_1(sK3),k2_zfmisc_1(sK2,sK1)) != iProver_top ),
% 7.48/1.48      inference(demodulation,[status(thm)],[c_11889,c_6523]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29523,plain,
% 7.48/1.48      ( v1_funct_2(k4_relat_1(k1_xboole_0),sK2,sK1) != iProver_top
% 7.48/1.48      | r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(sK2,sK1)) != iProver_top ),
% 7.48/1.48      inference(demodulation,[status(thm)],[c_29414,c_11893]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29563,plain,
% 7.48/1.48      ( k2_relset_1(sK1,sK2,k1_xboole_0) = sK2 ),
% 7.48/1.48      inference(demodulation,[status(thm)],[c_29414,c_56]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4199,plain,
% 7.48/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.48/1.48      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_5539,plain,
% 7.48/1.48      ( r1_tarski(k1_relat_1(k6_partfun1(X0)),X0) = iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_4214,c_4199]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_22,plain,
% 7.48/1.48      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 7.48/1.48      inference(cnf_transformation,[],[f149]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_5544,plain,
% 7.48/1.48      ( r1_tarski(X0,X0) = iProver_top ),
% 7.48/1.48      inference(light_normalisation,[status(thm)],[c_5539,c_22]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_1,plain,
% 7.48/1.48      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.48/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4244,plain,
% 7.48/1.48      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.48/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_3,plain,
% 7.48/1.48      ( v1_xboole_0(k1_xboole_0) ),
% 7.48/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_8,plain,
% 7.48/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.48/1.48      | ~ r2_hidden(X2,X0)
% 7.48/1.48      | ~ v1_xboole_0(X1) ),
% 7.48/1.48      inference(cnf_transformation,[],[f94]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_438,plain,
% 7.48/1.48      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.48/1.48      inference(prop_impl,[status(thm)],[c_6]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_439,plain,
% 7.48/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.48/1.48      inference(renaming,[status(thm)],[c_438]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_524,plain,
% 7.48/1.48      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 7.48/1.48      inference(bin_hyper_res,[status(thm)],[c_8,c_439]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_703,plain,
% 7.48/1.48      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | k1_xboole_0 != X2 ),
% 7.48/1.48      inference(resolution_lifted,[status(thm)],[c_3,c_524]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_704,plain,
% 7.48/1.48      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,k1_xboole_0) ),
% 7.48/1.48      inference(unflattening,[status(thm)],[c_703]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4201,plain,
% 7.48/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.48/1.48      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_6469,plain,
% 7.48/1.48      ( r1_tarski(X0,X1) = iProver_top
% 7.48/1.48      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_4244,c_4201]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_6638,plain,
% 7.48/1.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_5544,c_6469]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_9197,plain,
% 7.48/1.48      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.48/1.48      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_4241,c_4215]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_25359,plain,
% 7.48/1.48      ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_6638,c_9197]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_24,plain,
% 7.48/1.48      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 7.48/1.48      inference(cnf_transformation,[],[f151]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4790,plain,
% 7.48/1.48      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_24,c_21]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_25381,plain,
% 7.48/1.48      ( k2_relset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 7.48/1.48      inference(light_normalisation,[status(thm)],[c_25359,c_4790]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29565,plain,
% 7.48/1.48      ( sK2 = k1_xboole_0 ),
% 7.48/1.48      inference(demodulation,[status(thm)],[c_29563,c_25381]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29617,plain,
% 7.48/1.48      ( v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK1) != iProver_top
% 7.48/1.48      | r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK1)) != iProver_top ),
% 7.48/1.48      inference(light_normalisation,[status(thm)],[c_29523,c_29565]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_32,plain,
% 7.48/1.48      ( v1_relat_1(k6_partfun1(X0)) ),
% 7.48/1.48      inference(cnf_transformation,[],[f155]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4223,plain,
% 7.48/1.48      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_5179,plain,
% 7.48/1.48      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_24,c_4223]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_5873,plain,
% 7.48/1.48      ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_5179,c_4234]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_5875,plain,
% 7.48/1.48      ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 7.48/1.48      inference(light_normalisation,[status(thm)],[c_5873,c_4790]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_18,plain,
% 7.48/1.48      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 7.48/1.48      inference(cnf_transformation,[],[f103]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4232,plain,
% 7.48/1.48      ( k1_relat_1(X0) != k1_xboole_0
% 7.48/1.48      | k1_xboole_0 = X0
% 7.48/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_7145,plain,
% 7.48/1.48      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
% 7.48/1.48      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_5875,c_4232]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_170,plain,
% 7.48/1.48      ( v1_relat_1(X0) != iProver_top
% 7.48/1.48      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_172,plain,
% 7.48/1.48      ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
% 7.48/1.48      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_170]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_17141,plain,
% 7.48/1.48      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.48/1.48      inference(global_propositional_subsumption,
% 7.48/1.48                [status(thm)],
% 7.48/1.48                [c_7145,c_172,c_5179]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_29620,plain,
% 7.48/1.48      ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) != iProver_top
% 7.48/1.48      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK1)) != iProver_top ),
% 7.48/1.48      inference(light_normalisation,[status(thm)],[c_29617,c_17141]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_5436,plain,
% 7.48/1.48      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X0) = iProver_top
% 7.48/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_24,c_4200]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_5437,plain,
% 7.48/1.48      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 7.48/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.48/1.48      inference(light_normalisation,[status(thm)],[c_5436,c_24]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4224,plain,
% 7.48/1.48      ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_5287,plain,
% 7.48/1.48      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_24,c_4224]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_5439,plain,
% 7.48/1.48      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 7.48/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 7.48/1.48      inference(instantiation,[status(thm)],[c_5437]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_5538,plain,
% 7.48/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_24,c_4214]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_51,plain,
% 7.48/1.48      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.48/1.48      | v1_funct_2(X0,k1_xboole_0,X2)
% 7.48/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.48/1.48      | ~ r1_tarski(X1,X2)
% 7.48/1.48      | ~ v1_funct_1(X0) ),
% 7.48/1.48      inference(cnf_transformation,[],[f159]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_4209,plain,
% 7.48/1.48      ( v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
% 7.48/1.48      | v1_funct_2(X0,k1_xboole_0,X2) = iProver_top
% 7.48/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 7.48/1.48      | r1_tarski(X1,X2) != iProver_top
% 7.48/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.48/1.48      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_6702,plain,
% 7.48/1.48      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 7.48/1.48      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
% 7.48/1.48      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 7.48/1.48      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 7.48/1.48      inference(superposition,[status(thm)],[c_5538,c_4209]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_7923,plain,
% 7.48/1.48      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 7.48/1.48      inference(global_propositional_subsumption,
% 7.48/1.48                [status(thm)],
% 7.48/1.48                [c_5437,c_5287,c_5439,c_5538,c_6638,c_6702]) ).
% 7.48/1.48  
% 7.48/1.48  cnf(c_30462,plain,
% 7.48/1.48      ( $false ),
% 7.48/1.48      inference(forward_subsumption_resolution,
% 7.48/1.48                [status(thm)],
% 7.48/1.48                [c_29620,c_6638,c_7923]) ).
% 7.48/1.48  
% 7.48/1.48  
% 7.48/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.48/1.48  
% 7.48/1.48  ------                               Statistics
% 7.48/1.48  
% 7.48/1.48  ------ General
% 7.48/1.48  
% 7.48/1.48  abstr_ref_over_cycles:                  0
% 7.48/1.48  abstr_ref_under_cycles:                 0
% 7.48/1.48  gc_basic_clause_elim:                   0
% 7.48/1.48  forced_gc_time:                         0
% 7.48/1.48  parsing_time:                           0.012
% 7.48/1.48  unif_index_cands_time:                  0.
% 7.48/1.48  unif_index_add_time:                    0.
% 7.48/1.48  orderings_time:                         0.
% 7.48/1.48  out_proof_time:                         0.025
% 7.48/1.48  total_time:                             0.907
% 7.48/1.48  num_of_symbols:                         59
% 7.48/1.48  num_of_terms:                           25793
% 7.48/1.48  
% 7.48/1.48  ------ Preprocessing
% 7.48/1.48  
% 7.48/1.48  num_of_splits:                          0
% 7.48/1.48  num_of_split_atoms:                     0
% 7.48/1.48  num_of_reused_defs:                     0
% 7.48/1.48  num_eq_ax_congr_red:                    27
% 7.48/1.48  num_of_sem_filtered_clauses:            1
% 7.48/1.48  num_of_subtypes:                        0
% 7.48/1.48  monotx_restored_types:                  0
% 7.48/1.48  sat_num_of_epr_types:                   0
% 7.48/1.48  sat_num_of_non_cyclic_types:            0
% 7.48/1.48  sat_guarded_non_collapsed_types:        0
% 7.48/1.48  num_pure_diseq_elim:                    0
% 7.48/1.48  simp_replaced_by:                       0
% 7.48/1.48  res_preprocessed:                       253
% 7.48/1.48  prep_upred:                             0
% 7.48/1.48  prep_unflattend:                        153
% 7.48/1.48  smt_new_axioms:                         0
% 7.48/1.48  pred_elim_cands:                        7
% 7.48/1.48  pred_elim:                              3
% 7.48/1.48  pred_elim_cl:                           4
% 7.48/1.48  pred_elim_cycles:                       7
% 7.48/1.48  merged_defs:                            8
% 7.48/1.48  merged_defs_ncl:                        0
% 7.48/1.48  bin_hyper_res:                          9
% 7.48/1.48  prep_cycles:                            4
% 7.48/1.48  pred_elim_time:                         0.058
% 7.48/1.48  splitting_time:                         0.
% 7.48/1.48  sem_filter_time:                        0.
% 7.48/1.48  monotx_time:                            0.001
% 7.48/1.48  subtype_inf_time:                       0.
% 7.48/1.48  
% 7.48/1.48  ------ Problem properties
% 7.48/1.48  
% 7.48/1.48  clauses:                                52
% 7.48/1.48  conjectures:                            6
% 7.48/1.48  epr:                                    5
% 7.48/1.48  horn:                                   49
% 7.48/1.48  ground:                                 7
% 7.48/1.48  unary:                                  14
% 7.48/1.48  binary:                                 17
% 7.48/1.48  lits:                                   134
% 7.48/1.48  lits_eq:                                32
% 7.48/1.48  fd_pure:                                0
% 7.48/1.48  fd_pseudo:                              0
% 7.48/1.48  fd_cond:                                4
% 7.48/1.48  fd_pseudo_cond:                         1
% 7.48/1.48  ac_symbols:                             0
% 7.48/1.48  
% 7.48/1.48  ------ Propositional Solver
% 7.48/1.48  
% 7.48/1.48  prop_solver_calls:                      30
% 7.48/1.48  prop_fast_solver_calls:                 2829
% 7.48/1.48  smt_solver_calls:                       0
% 7.48/1.48  smt_fast_solver_calls:                  0
% 7.48/1.48  prop_num_of_clauses:                    10025
% 7.48/1.48  prop_preprocess_simplified:             23367
% 7.48/1.48  prop_fo_subsumed:                       149
% 7.48/1.48  prop_solver_time:                       0.
% 7.48/1.48  smt_solver_time:                        0.
% 7.48/1.48  smt_fast_solver_time:                   0.
% 7.48/1.48  prop_fast_solver_time:                  0.
% 7.48/1.48  prop_unsat_core_time:                   0.
% 7.48/1.48  
% 7.48/1.48  ------ QBF
% 7.48/1.48  
% 7.48/1.48  qbf_q_res:                              0
% 7.48/1.48  qbf_num_tautologies:                    0
% 7.48/1.48  qbf_prep_cycles:                        0
% 7.48/1.48  
% 7.48/1.48  ------ BMC1
% 7.48/1.48  
% 7.48/1.48  bmc1_current_bound:                     -1
% 7.48/1.48  bmc1_last_solved_bound:                 -1
% 7.48/1.48  bmc1_unsat_core_size:                   -1
% 7.48/1.48  bmc1_unsat_core_parents_size:           -1
% 7.48/1.48  bmc1_merge_next_fun:                    0
% 7.48/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.48/1.48  
% 7.48/1.48  ------ Instantiation
% 7.48/1.48  
% 7.48/1.48  inst_num_of_clauses:                    2673
% 7.48/1.48  inst_num_in_passive:                    1192
% 7.48/1.48  inst_num_in_active:                     1223
% 7.48/1.48  inst_num_in_unprocessed:                260
% 7.48/1.48  inst_num_of_loops:                      1640
% 7.48/1.48  inst_num_of_learning_restarts:          0
% 7.48/1.48  inst_num_moves_active_passive:          415
% 7.48/1.48  inst_lit_activity:                      0
% 7.48/1.48  inst_lit_activity_moves:                1
% 7.48/1.48  inst_num_tautologies:                   0
% 7.48/1.48  inst_num_prop_implied:                  0
% 7.48/1.48  inst_num_existing_simplified:           0
% 7.48/1.48  inst_num_eq_res_simplified:             0
% 7.48/1.48  inst_num_child_elim:                    0
% 7.48/1.48  inst_num_of_dismatching_blockings:      1011
% 7.48/1.48  inst_num_of_non_proper_insts:           2770
% 7.48/1.48  inst_num_of_duplicates:                 0
% 7.48/1.48  inst_inst_num_from_inst_to_res:         0
% 7.48/1.48  inst_dismatching_checking_time:         0.
% 7.48/1.48  
% 7.48/1.48  ------ Resolution
% 7.48/1.48  
% 7.48/1.48  res_num_of_clauses:                     0
% 7.48/1.48  res_num_in_passive:                     0
% 7.48/1.48  res_num_in_active:                      0
% 7.48/1.48  res_num_of_loops:                       257
% 7.48/1.48  res_forward_subset_subsumed:            43
% 7.48/1.48  res_backward_subset_subsumed:           8
% 7.48/1.48  res_forward_subsumed:                   0
% 7.48/1.48  res_backward_subsumed:                  0
% 7.48/1.48  res_forward_subsumption_resolution:     2
% 7.48/1.48  res_backward_subsumption_resolution:    0
% 7.48/1.48  res_clause_to_clause_subsumption:       2162
% 7.48/1.48  res_orphan_elimination:                 0
% 7.48/1.48  res_tautology_del:                      104
% 7.48/1.48  res_num_eq_res_simplified:              0
% 7.48/1.48  res_num_sel_changes:                    0
% 7.48/1.48  res_moves_from_active_to_pass:          0
% 7.48/1.48  
% 7.48/1.48  ------ Superposition
% 7.48/1.48  
% 7.48/1.48  sup_time_total:                         0.
% 7.48/1.48  sup_time_generating:                    0.
% 7.48/1.48  sup_time_sim_full:                      0.
% 7.48/1.48  sup_time_sim_immed:                     0.
% 7.48/1.48  
% 7.48/1.48  sup_num_of_clauses:                     424
% 7.48/1.48  sup_num_in_active:                      151
% 7.48/1.48  sup_num_in_passive:                     273
% 7.48/1.48  sup_num_of_loops:                       326
% 7.48/1.48  sup_fw_superposition:                   447
% 7.48/1.48  sup_bw_superposition:                   385
% 7.48/1.48  sup_immediate_simplified:               402
% 7.48/1.48  sup_given_eliminated:                   0
% 7.48/1.48  comparisons_done:                       0
% 7.48/1.48  comparisons_avoided:                    36
% 7.48/1.48  
% 7.48/1.48  ------ Simplifications
% 7.48/1.48  
% 7.48/1.48  
% 7.48/1.48  sim_fw_subset_subsumed:                 77
% 7.48/1.48  sim_bw_subset_subsumed:                 33
% 7.48/1.48  sim_fw_subsumed:                        42
% 7.48/1.48  sim_bw_subsumed:                        1
% 7.48/1.48  sim_fw_subsumption_res:                 6
% 7.48/1.48  sim_bw_subsumption_res:                 0
% 7.48/1.48  sim_tautology_del:                      19
% 7.48/1.48  sim_eq_tautology_del:                   97
% 7.48/1.48  sim_eq_res_simp:                        10
% 7.48/1.48  sim_fw_demodulated:                     28
% 7.48/1.48  sim_bw_demodulated:                     167
% 7.48/1.48  sim_light_normalised:                   300
% 7.48/1.48  sim_joinable_taut:                      0
% 7.48/1.48  sim_joinable_simp:                      0
% 7.48/1.48  sim_ac_normalised:                      0
% 7.48/1.48  sim_smt_subsumption:                    0
% 7.48/1.48  
%------------------------------------------------------------------------------
