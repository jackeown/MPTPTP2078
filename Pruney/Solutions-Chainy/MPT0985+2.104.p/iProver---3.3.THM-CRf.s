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
% DateTime   : Thu Dec  3 12:02:41 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  241 (17069 expanded)
%              Number of clauses        :  178 (6042 expanded)
%              Number of leaves         :   19 (3129 expanded)
%              Depth                    :   29
%              Number of atoms          :  689 (89401 expanded)
%              Number of equality atoms :  367 (17859 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f28])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f32])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & k2_relset_1(sK0,sK1,sK2) = sK1
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36])).

fof(f62,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f46,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f56])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f55])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1076,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_1077,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1076])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1079,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1077,c_26])).

cnf(c_1352,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_1079])).

cnf(c_1365,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1860,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1365])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1369,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k1_relset_1(X1_46,X2_46,X0_46) = k1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1857,plain,
    ( k1_relset_1(X0_46,X1_46,X2_46) = k1_relat_1(X2_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1369])).

cnf(c_2626,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1860,c_1857])).

cnf(c_2791,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1352,c_2626])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_338,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_339,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_341,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_28])).

cnf(c_1361,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_341])).

cnf(c_1864,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1361])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1371,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2104,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1371])).

cnf(c_2131,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1864,c_26,c_1361,c_2104])).

cnf(c_20,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1367,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_46),k2_relat_1(X0_46))))
    | ~ v1_funct_1(X0_46)
    | ~ v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1859,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_46),k2_relat_1(X0_46)))) = iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1367])).

cnf(c_3025,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2131,c_1859])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1368,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | k2_relset_1(X1_46,X2_46,X0_46) = k2_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1858,plain,
    ( k2_relset_1(X0_46,X1_46,X2_46) = k2_relat_1(X2_46)
    | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1368])).

cnf(c_2710,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1860,c_1858])).

cnf(c_24,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1366,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_2715,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2710,c_1366])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_324,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_325,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_327,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_28])).

cnf(c_1362,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_327])).

cnf(c_1863,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1362])).

cnf(c_2127,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1863,c_26,c_1362,c_2104])).

cnf(c_2721,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2715,c_2127])).

cnf(c_3053,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3025,c_2721])).

cnf(c_29,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1372,plain,
    ( ~ v1_funct_1(X0_46)
    | ~ v1_relat_1(X0_46)
    | v1_relat_1(k2_funct_1(X0_46)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2094,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_2095,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2094])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1373,plain,
    ( ~ v1_funct_1(X0_46)
    | v1_funct_1(k2_funct_1(X0_46))
    | ~ v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2097,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_2098,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2097])).

cnf(c_2105,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2104])).

cnf(c_3583,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3053,c_29,c_31,c_2095,c_2098,c_2105])).

cnf(c_3592,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3583,c_1857])).

cnf(c_3594,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3592,c_2721])).

cnf(c_3733,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2791,c_3594])).

cnf(c_21,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1087,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k2_relat_1(X0) != sK0
    | k1_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_23])).

cnf(c_1088,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_1087])).

cnf(c_1100,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1088,c_10])).

cnf(c_1351,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(subtyping,[status(esa)],[c_1100])).

cnf(c_1873,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1351])).

cnf(c_1447,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1351])).

cnf(c_2511,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1873,c_29,c_31,c_1447,c_2098,c_2105])).

cnf(c_2512,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2511])).

cnf(c_2515,plain,
    ( k2_relat_1(sK2) != sK1
    | k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2512,c_2127,c_2131])).

cnf(c_2719,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2715,c_2515])).

cnf(c_2728,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2719])).

cnf(c_2966,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2791,c_2728])).

cnf(c_3588,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2791,c_3583])).

cnf(c_3776,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3733,c_2966,c_3588])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_961,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK0 != X1
    | sK1 != k1_xboole_0
    | sK2 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_962,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_961])).

cnf(c_1358,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_962])).

cnf(c_1867,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1358])).

cnf(c_3792,plain,
    ( sK0 = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3776,c_1867])).

cnf(c_3828,plain,
    ( sK0 = k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3792])).

cnf(c_3799,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3776,c_1860])).

cnf(c_3832,plain,
    ( sK0 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3828,c_3799])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_96,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1370,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
    | ~ v1_xboole_0(X1_46)
    | v1_xboole_0(X0_46) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2392,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | ~ v1_xboole_0(X0_46)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_2393,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
    | v1_xboole_0(X0_46) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2392])).

cnf(c_2395,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2393])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1376,plain,
    ( ~ v1_xboole_0(X0_46)
    | ~ v1_xboole_0(X1_46)
    | X0_46 = X1_46 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2439,plain,
    ( ~ v1_xboole_0(X0_46)
    | ~ v1_xboole_0(sK2)
    | sK2 = X0_46 ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_2440,plain,
    ( sK2 = X0_46
    | v1_xboole_0(X0_46) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2439])).

cnf(c_2442,plain,
    ( sK2 = k1_xboole_0
    | v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2440])).

cnf(c_3024,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2715,c_1859])).

cnf(c_3390,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3024,c_29,c_31,c_2105])).

cnf(c_3784,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3776,c_3390])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1375,plain,
    ( ~ v1_relat_1(X0_46)
    | k2_relat_1(X0_46) != k1_xboole_0
    | k1_relat_1(X0_46) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1851,plain,
    ( k2_relat_1(X0_46) != k1_xboole_0
    | k1_relat_1(X0_46) = k1_xboole_0
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1375])).

cnf(c_2734,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK1 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2715,c_1851])).

cnf(c_2851,plain,
    ( sK1 != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2734,c_31,c_2105])).

cnf(c_2852,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2851])).

cnf(c_3787,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3776,c_2852])).

cnf(c_3841,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3787])).

cnf(c_3852,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3784,c_3841])).

cnf(c_4168,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3832,c_96,c_2395,c_2442,c_3852])).

cnf(c_3791,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3776,c_2715])).

cnf(c_4174,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4168,c_3791])).

cnf(c_4305,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4174,c_1851])).

cnf(c_1379,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_1406,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1379])).

cnf(c_1412,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_2107,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1371])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_309,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_310,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_1363,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_310])).

cnf(c_2108,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) ),
    inference(instantiation,[status(thm)],[c_1363])).

cnf(c_2240,plain,
    ( ~ v1_xboole_0(X0_46)
    | ~ v1_xboole_0(sK2)
    | X0_46 = sK2 ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_2241,plain,
    ( X0_46 = sK2
    | v1_xboole_0(X0_46) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2240])).

cnf(c_2243,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2241])).

cnf(c_2321,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2131,c_1851])).

cnf(c_2322,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2321,c_2127])).

cnf(c_1382,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_2578,plain,
    ( k2_relat_1(sK2) != X0_46
    | k1_xboole_0 != X0_46
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1382])).

cnf(c_2579,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2578])).

cnf(c_2419,plain,
    ( k2_relat_1(X0_46) != X1_46
    | k2_relat_1(X0_46) = k1_xboole_0
    | k1_xboole_0 != X1_46 ),
    inference(instantiation,[status(thm)],[c_1382])).

cnf(c_2780,plain,
    ( k2_relat_1(X0_46) != k2_relat_1(X1_46)
    | k2_relat_1(X0_46) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(X1_46) ),
    inference(instantiation,[status(thm)],[c_2419])).

cnf(c_3428,plain,
    ( k2_relat_1(X0_46) != k2_relat_1(sK2)
    | k2_relat_1(X0_46) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2780])).

cnf(c_3429,plain,
    ( k2_relat_1(k1_xboole_0) != k2_relat_1(sK2)
    | k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3428])).

cnf(c_1387,plain,
    ( X0_46 != X1_46
    | k2_relat_1(X0_46) = k2_relat_1(X1_46) ),
    theory(equality)).

cnf(c_3650,plain,
    ( X0_46 != sK2
    | k2_relat_1(X0_46) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1387])).

cnf(c_3652,plain,
    ( k2_relat_1(k1_xboole_0) = k2_relat_1(sK2)
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_3650])).

cnf(c_4320,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4305,c_29,c_31,c_96,c_1406,c_1412,c_2095,c_2105,c_2107,c_2108,c_2243,c_2322,c_2395,c_2579,c_2734,c_2966,c_3429,c_3588,c_3652,c_3852])).

cnf(c_1862,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1363])).

cnf(c_2627,plain,
    ( k1_relset_1(X0_46,X1_46,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1862,c_1857])).

cnf(c_4323,plain,
    ( k1_relset_1(X0_46,X1_46,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4320,c_2627])).

cnf(c_16,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1004,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_1005,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1004])).

cnf(c_1356,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1005])).

cnf(c_1869,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1356])).

cnf(c_1441,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1356])).

cnf(c_2468,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sK1 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1869,c_29,c_31,c_1441,c_2098,c_2105])).

cnf(c_2469,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2468])).

cnf(c_3793,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3776,c_2469])).

cnf(c_3823,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3793])).

cnf(c_1856,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
    | v1_xboole_0(X1_46) != iProver_top
    | v1_xboole_0(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1370])).

cnf(c_3589,plain,
    ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3583,c_1856])).

cnf(c_2185,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1367])).

cnf(c_2197,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2185])).

cnf(c_1383,plain,
    ( ~ v1_xboole_0(X0_46)
    | v1_xboole_0(X1_46)
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_2526,plain,
    ( ~ v1_xboole_0(X0_46)
    | v1_xboole_0(k1_relat_1(X1_46))
    | k1_relat_1(X1_46) != X0_46 ),
    inference(instantiation,[status(thm)],[c_1383])).

cnf(c_2924,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v1_xboole_0(k1_relat_1(k2_funct_1(sK2)))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2526])).

cnf(c_2925,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | v1_xboole_0(k2_relat_1(sK2)) != iProver_top
    | v1_xboole_0(k1_relat_1(k2_funct_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2924])).

cnf(c_2554,plain,
    ( ~ v1_xboole_0(X0_46)
    | v1_xboole_0(k2_relat_1(X1_46))
    | k2_relat_1(X1_46) != X0_46 ),
    inference(instantiation,[status(thm)],[c_1383])).

cnf(c_3217,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2554])).

cnf(c_3218,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | v1_xboole_0(k2_relat_1(sK2)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3217])).

cnf(c_2669,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | ~ v1_xboole_0(X0_46)
    | v1_xboole_0(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_3256,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | v1_xboole_0(k2_funct_1(sK2))
    | ~ v1_xboole_0(k1_relat_1(k2_funct_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_2669])).

cnf(c_3257,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) != iProver_top
    | v1_xboole_0(k2_funct_1(sK2)) = iProver_top
    | v1_xboole_0(k1_relat_1(k2_funct_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3256])).

cnf(c_3720,plain,
    ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3589,c_29,c_26,c_31,c_96,c_1362,c_2095,c_2098,c_2104,c_2105,c_2197,c_2322,c_2734,c_2925,c_2966,c_3218,c_3257,c_3588])).

cnf(c_1377,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1849,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1377])).

cnf(c_1850,plain,
    ( X0_46 = X1_46
    | v1_xboole_0(X1_46) != iProver_top
    | v1_xboole_0(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1376])).

cnf(c_2232,plain,
    ( k1_xboole_0 = X0_46
    | v1_xboole_0(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1850])).

cnf(c_3726,plain,
    ( k2_funct_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3720,c_2232])).

cnf(c_4740,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3726,c_4168])).

cnf(c_5054,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3823,c_4168,c_4740])).

cnf(c_5057,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5054,c_1862])).

cnf(c_5308,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4323,c_5057])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5308,c_1406])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:35:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.74/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/0.99  
% 2.74/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.74/0.99  
% 2.74/0.99  ------  iProver source info
% 2.74/0.99  
% 2.74/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.74/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.74/0.99  git: non_committed_changes: false
% 2.74/0.99  git: last_make_outside_of_git: false
% 2.74/0.99  
% 2.74/0.99  ------ 
% 2.74/0.99  
% 2.74/0.99  ------ Input Options
% 2.74/0.99  
% 2.74/0.99  --out_options                           all
% 2.74/0.99  --tptp_safe_out                         true
% 2.74/0.99  --problem_path                          ""
% 2.74/0.99  --include_path                          ""
% 2.74/0.99  --clausifier                            res/vclausify_rel
% 2.74/0.99  --clausifier_options                    --mode clausify
% 2.74/0.99  --stdin                                 false
% 2.74/0.99  --stats_out                             all
% 2.74/0.99  
% 2.74/0.99  ------ General Options
% 2.74/0.99  
% 2.74/0.99  --fof                                   false
% 2.74/0.99  --time_out_real                         305.
% 2.74/0.99  --time_out_virtual                      -1.
% 2.74/0.99  --symbol_type_check                     false
% 2.74/0.99  --clausify_out                          false
% 2.74/0.99  --sig_cnt_out                           false
% 2.74/0.99  --trig_cnt_out                          false
% 2.74/0.99  --trig_cnt_out_tolerance                1.
% 2.74/0.99  --trig_cnt_out_sk_spl                   false
% 2.74/0.99  --abstr_cl_out                          false
% 2.74/0.99  
% 2.74/0.99  ------ Global Options
% 2.74/0.99  
% 2.74/0.99  --schedule                              default
% 2.74/0.99  --add_important_lit                     false
% 2.74/0.99  --prop_solver_per_cl                    1000
% 2.74/0.99  --min_unsat_core                        false
% 2.74/0.99  --soft_assumptions                      false
% 2.74/0.99  --soft_lemma_size                       3
% 2.74/0.99  --prop_impl_unit_size                   0
% 2.74/0.99  --prop_impl_unit                        []
% 2.74/0.99  --share_sel_clauses                     true
% 2.74/0.99  --reset_solvers                         false
% 2.74/0.99  --bc_imp_inh                            [conj_cone]
% 2.74/0.99  --conj_cone_tolerance                   3.
% 2.74/0.99  --extra_neg_conj                        none
% 2.74/0.99  --large_theory_mode                     true
% 2.74/0.99  --prolific_symb_bound                   200
% 2.74/0.99  --lt_threshold                          2000
% 2.74/0.99  --clause_weak_htbl                      true
% 2.74/0.99  --gc_record_bc_elim                     false
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing Options
% 2.74/0.99  
% 2.74/0.99  --preprocessing_flag                    true
% 2.74/0.99  --time_out_prep_mult                    0.1
% 2.74/0.99  --splitting_mode                        input
% 2.74/0.99  --splitting_grd                         true
% 2.74/0.99  --splitting_cvd                         false
% 2.74/0.99  --splitting_cvd_svl                     false
% 2.74/0.99  --splitting_nvd                         32
% 2.74/0.99  --sub_typing                            true
% 2.74/0.99  --prep_gs_sim                           true
% 2.74/0.99  --prep_unflatten                        true
% 2.74/0.99  --prep_res_sim                          true
% 2.74/0.99  --prep_upred                            true
% 2.74/0.99  --prep_sem_filter                       exhaustive
% 2.74/0.99  --prep_sem_filter_out                   false
% 2.74/0.99  --pred_elim                             true
% 2.74/0.99  --res_sim_input                         true
% 2.74/0.99  --eq_ax_congr_red                       true
% 2.74/0.99  --pure_diseq_elim                       true
% 2.74/0.99  --brand_transform                       false
% 2.74/0.99  --non_eq_to_eq                          false
% 2.74/0.99  --prep_def_merge                        true
% 2.74/0.99  --prep_def_merge_prop_impl              false
% 2.74/0.99  --prep_def_merge_mbd                    true
% 2.74/0.99  --prep_def_merge_tr_red                 false
% 2.74/0.99  --prep_def_merge_tr_cl                  false
% 2.74/0.99  --smt_preprocessing                     true
% 2.74/0.99  --smt_ac_axioms                         fast
% 2.74/0.99  --preprocessed_out                      false
% 2.74/0.99  --preprocessed_stats                    false
% 2.74/0.99  
% 2.74/0.99  ------ Abstraction refinement Options
% 2.74/0.99  
% 2.74/0.99  --abstr_ref                             []
% 2.74/0.99  --abstr_ref_prep                        false
% 2.74/0.99  --abstr_ref_until_sat                   false
% 2.74/0.99  --abstr_ref_sig_restrict                funpre
% 2.74/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.99  --abstr_ref_under                       []
% 2.74/0.99  
% 2.74/0.99  ------ SAT Options
% 2.74/0.99  
% 2.74/0.99  --sat_mode                              false
% 2.74/0.99  --sat_fm_restart_options                ""
% 2.74/0.99  --sat_gr_def                            false
% 2.74/0.99  --sat_epr_types                         true
% 2.74/0.99  --sat_non_cyclic_types                  false
% 2.74/0.99  --sat_finite_models                     false
% 2.74/0.99  --sat_fm_lemmas                         false
% 2.74/0.99  --sat_fm_prep                           false
% 2.74/0.99  --sat_fm_uc_incr                        true
% 2.74/0.99  --sat_out_model                         small
% 2.74/0.99  --sat_out_clauses                       false
% 2.74/0.99  
% 2.74/0.99  ------ QBF Options
% 2.74/0.99  
% 2.74/0.99  --qbf_mode                              false
% 2.74/0.99  --qbf_elim_univ                         false
% 2.74/0.99  --qbf_dom_inst                          none
% 2.74/0.99  --qbf_dom_pre_inst                      false
% 2.74/0.99  --qbf_sk_in                             false
% 2.74/0.99  --qbf_pred_elim                         true
% 2.74/0.99  --qbf_split                             512
% 2.74/0.99  
% 2.74/0.99  ------ BMC1 Options
% 2.74/0.99  
% 2.74/0.99  --bmc1_incremental                      false
% 2.74/0.99  --bmc1_axioms                           reachable_all
% 2.74/0.99  --bmc1_min_bound                        0
% 2.74/0.99  --bmc1_max_bound                        -1
% 2.74/0.99  --bmc1_max_bound_default                -1
% 2.74/0.99  --bmc1_symbol_reachability              true
% 2.74/0.99  --bmc1_property_lemmas                  false
% 2.74/0.99  --bmc1_k_induction                      false
% 2.74/0.99  --bmc1_non_equiv_states                 false
% 2.74/0.99  --bmc1_deadlock                         false
% 2.74/0.99  --bmc1_ucm                              false
% 2.74/0.99  --bmc1_add_unsat_core                   none
% 2.74/0.99  --bmc1_unsat_core_children              false
% 2.74/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.99  --bmc1_out_stat                         full
% 2.74/0.99  --bmc1_ground_init                      false
% 2.74/0.99  --bmc1_pre_inst_next_state              false
% 2.74/0.99  --bmc1_pre_inst_state                   false
% 2.74/0.99  --bmc1_pre_inst_reach_state             false
% 2.74/0.99  --bmc1_out_unsat_core                   false
% 2.74/0.99  --bmc1_aig_witness_out                  false
% 2.74/0.99  --bmc1_verbose                          false
% 2.74/0.99  --bmc1_dump_clauses_tptp                false
% 2.74/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.99  --bmc1_dump_file                        -
% 2.74/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.99  --bmc1_ucm_extend_mode                  1
% 2.74/0.99  --bmc1_ucm_init_mode                    2
% 2.74/0.99  --bmc1_ucm_cone_mode                    none
% 2.74/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.99  --bmc1_ucm_relax_model                  4
% 2.74/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.99  --bmc1_ucm_layered_model                none
% 2.74/0.99  --bmc1_ucm_max_lemma_size               10
% 2.74/0.99  
% 2.74/0.99  ------ AIG Options
% 2.74/0.99  
% 2.74/0.99  --aig_mode                              false
% 2.74/0.99  
% 2.74/0.99  ------ Instantiation Options
% 2.74/0.99  
% 2.74/0.99  --instantiation_flag                    true
% 2.74/0.99  --inst_sos_flag                         false
% 2.74/0.99  --inst_sos_phase                        true
% 2.74/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.99  --inst_lit_sel_side                     num_symb
% 2.74/0.99  --inst_solver_per_active                1400
% 2.74/0.99  --inst_solver_calls_frac                1.
% 2.74/0.99  --inst_passive_queue_type               priority_queues
% 2.74/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.99  --inst_passive_queues_freq              [25;2]
% 2.74/0.99  --inst_dismatching                      true
% 2.74/0.99  --inst_eager_unprocessed_to_passive     true
% 2.74/0.99  --inst_prop_sim_given                   true
% 2.74/0.99  --inst_prop_sim_new                     false
% 2.74/0.99  --inst_subs_new                         false
% 2.74/0.99  --inst_eq_res_simp                      false
% 2.74/0.99  --inst_subs_given                       false
% 2.74/0.99  --inst_orphan_elimination               true
% 2.74/0.99  --inst_learning_loop_flag               true
% 2.74/0.99  --inst_learning_start                   3000
% 2.74/0.99  --inst_learning_factor                  2
% 2.74/0.99  --inst_start_prop_sim_after_learn       3
% 2.74/0.99  --inst_sel_renew                        solver
% 2.74/0.99  --inst_lit_activity_flag                true
% 2.74/0.99  --inst_restr_to_given                   false
% 2.74/0.99  --inst_activity_threshold               500
% 2.74/0.99  --inst_out_proof                        true
% 2.74/0.99  
% 2.74/0.99  ------ Resolution Options
% 2.74/0.99  
% 2.74/0.99  --resolution_flag                       true
% 2.74/0.99  --res_lit_sel                           adaptive
% 2.74/0.99  --res_lit_sel_side                      none
% 2.74/0.99  --res_ordering                          kbo
% 2.74/0.99  --res_to_prop_solver                    active
% 2.74/0.99  --res_prop_simpl_new                    false
% 2.74/0.99  --res_prop_simpl_given                  true
% 2.74/0.99  --res_passive_queue_type                priority_queues
% 2.74/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.99  --res_passive_queues_freq               [15;5]
% 2.74/0.99  --res_forward_subs                      full
% 2.74/0.99  --res_backward_subs                     full
% 2.74/0.99  --res_forward_subs_resolution           true
% 2.74/0.99  --res_backward_subs_resolution          true
% 2.74/0.99  --res_orphan_elimination                true
% 2.74/0.99  --res_time_limit                        2.
% 2.74/0.99  --res_out_proof                         true
% 2.74/0.99  
% 2.74/0.99  ------ Superposition Options
% 2.74/0.99  
% 2.74/0.99  --superposition_flag                    true
% 2.74/0.99  --sup_passive_queue_type                priority_queues
% 2.74/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.99  --demod_completeness_check              fast
% 2.74/0.99  --demod_use_ground                      true
% 2.74/0.99  --sup_to_prop_solver                    passive
% 2.74/0.99  --sup_prop_simpl_new                    true
% 2.74/0.99  --sup_prop_simpl_given                  true
% 2.74/0.99  --sup_fun_splitting                     false
% 2.74/0.99  --sup_smt_interval                      50000
% 2.74/0.99  
% 2.74/0.99  ------ Superposition Simplification Setup
% 2.74/0.99  
% 2.74/0.99  --sup_indices_passive                   []
% 2.74/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_full_bw                           [BwDemod]
% 2.74/0.99  --sup_immed_triv                        [TrivRules]
% 2.74/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_immed_bw_main                     []
% 2.74/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.99  
% 2.74/0.99  ------ Combination Options
% 2.74/0.99  
% 2.74/0.99  --comb_res_mult                         3
% 2.74/0.99  --comb_sup_mult                         2
% 2.74/0.99  --comb_inst_mult                        10
% 2.74/0.99  
% 2.74/0.99  ------ Debug Options
% 2.74/0.99  
% 2.74/0.99  --dbg_backtrace                         false
% 2.74/0.99  --dbg_dump_prop_clauses                 false
% 2.74/0.99  --dbg_dump_prop_clauses_file            -
% 2.74/0.99  --dbg_out_stat                          false
% 2.74/0.99  ------ Parsing...
% 2.74/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.74/0.99  ------ Proving...
% 2.74/0.99  ------ Problem Properties 
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  clauses                                 28
% 2.74/0.99  conjectures                             3
% 2.74/0.99  EPR                                     3
% 2.74/0.99  Horn                                    24
% 2.74/0.99  unary                                   5
% 2.74/0.99  binary                                  6
% 2.74/0.99  lits                                    80
% 2.74/0.99  lits eq                                 35
% 2.74/0.99  fd_pure                                 0
% 2.74/0.99  fd_pseudo                               0
% 2.74/0.99  fd_cond                                 1
% 2.74/0.99  fd_pseudo_cond                          1
% 2.74/0.99  AC symbols                              0
% 2.74/0.99  
% 2.74/0.99  ------ Schedule dynamic 5 is on 
% 2.74/0.99  
% 2.74/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  ------ 
% 2.74/0.99  Current options:
% 2.74/0.99  ------ 
% 2.74/0.99  
% 2.74/0.99  ------ Input Options
% 2.74/0.99  
% 2.74/0.99  --out_options                           all
% 2.74/0.99  --tptp_safe_out                         true
% 2.74/0.99  --problem_path                          ""
% 2.74/0.99  --include_path                          ""
% 2.74/0.99  --clausifier                            res/vclausify_rel
% 2.74/0.99  --clausifier_options                    --mode clausify
% 2.74/0.99  --stdin                                 false
% 2.74/0.99  --stats_out                             all
% 2.74/0.99  
% 2.74/0.99  ------ General Options
% 2.74/0.99  
% 2.74/0.99  --fof                                   false
% 2.74/0.99  --time_out_real                         305.
% 2.74/0.99  --time_out_virtual                      -1.
% 2.74/0.99  --symbol_type_check                     false
% 2.74/0.99  --clausify_out                          false
% 2.74/0.99  --sig_cnt_out                           false
% 2.74/0.99  --trig_cnt_out                          false
% 2.74/0.99  --trig_cnt_out_tolerance                1.
% 2.74/0.99  --trig_cnt_out_sk_spl                   false
% 2.74/0.99  --abstr_cl_out                          false
% 2.74/0.99  
% 2.74/0.99  ------ Global Options
% 2.74/0.99  
% 2.74/0.99  --schedule                              default
% 2.74/0.99  --add_important_lit                     false
% 2.74/0.99  --prop_solver_per_cl                    1000
% 2.74/0.99  --min_unsat_core                        false
% 2.74/0.99  --soft_assumptions                      false
% 2.74/0.99  --soft_lemma_size                       3
% 2.74/0.99  --prop_impl_unit_size                   0
% 2.74/0.99  --prop_impl_unit                        []
% 2.74/0.99  --share_sel_clauses                     true
% 2.74/0.99  --reset_solvers                         false
% 2.74/0.99  --bc_imp_inh                            [conj_cone]
% 2.74/0.99  --conj_cone_tolerance                   3.
% 2.74/0.99  --extra_neg_conj                        none
% 2.74/0.99  --large_theory_mode                     true
% 2.74/0.99  --prolific_symb_bound                   200
% 2.74/0.99  --lt_threshold                          2000
% 2.74/0.99  --clause_weak_htbl                      true
% 2.74/0.99  --gc_record_bc_elim                     false
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing Options
% 2.74/0.99  
% 2.74/0.99  --preprocessing_flag                    true
% 2.74/0.99  --time_out_prep_mult                    0.1
% 2.74/0.99  --splitting_mode                        input
% 2.74/0.99  --splitting_grd                         true
% 2.74/0.99  --splitting_cvd                         false
% 2.74/0.99  --splitting_cvd_svl                     false
% 2.74/0.99  --splitting_nvd                         32
% 2.74/0.99  --sub_typing                            true
% 2.74/0.99  --prep_gs_sim                           true
% 2.74/0.99  --prep_unflatten                        true
% 2.74/0.99  --prep_res_sim                          true
% 2.74/0.99  --prep_upred                            true
% 2.74/0.99  --prep_sem_filter                       exhaustive
% 2.74/0.99  --prep_sem_filter_out                   false
% 2.74/0.99  --pred_elim                             true
% 2.74/0.99  --res_sim_input                         true
% 2.74/0.99  --eq_ax_congr_red                       true
% 2.74/0.99  --pure_diseq_elim                       true
% 2.74/0.99  --brand_transform                       false
% 2.74/0.99  --non_eq_to_eq                          false
% 2.74/0.99  --prep_def_merge                        true
% 2.74/0.99  --prep_def_merge_prop_impl              false
% 2.74/0.99  --prep_def_merge_mbd                    true
% 2.74/0.99  --prep_def_merge_tr_red                 false
% 2.74/0.99  --prep_def_merge_tr_cl                  false
% 2.74/0.99  --smt_preprocessing                     true
% 2.74/0.99  --smt_ac_axioms                         fast
% 2.74/0.99  --preprocessed_out                      false
% 2.74/0.99  --preprocessed_stats                    false
% 2.74/0.99  
% 2.74/0.99  ------ Abstraction refinement Options
% 2.74/0.99  
% 2.74/0.99  --abstr_ref                             []
% 2.74/0.99  --abstr_ref_prep                        false
% 2.74/0.99  --abstr_ref_until_sat                   false
% 2.74/0.99  --abstr_ref_sig_restrict                funpre
% 2.74/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.99  --abstr_ref_under                       []
% 2.74/0.99  
% 2.74/0.99  ------ SAT Options
% 2.74/0.99  
% 2.74/0.99  --sat_mode                              false
% 2.74/0.99  --sat_fm_restart_options                ""
% 2.74/0.99  --sat_gr_def                            false
% 2.74/0.99  --sat_epr_types                         true
% 2.74/0.99  --sat_non_cyclic_types                  false
% 2.74/0.99  --sat_finite_models                     false
% 2.74/0.99  --sat_fm_lemmas                         false
% 2.74/0.99  --sat_fm_prep                           false
% 2.74/0.99  --sat_fm_uc_incr                        true
% 2.74/0.99  --sat_out_model                         small
% 2.74/0.99  --sat_out_clauses                       false
% 2.74/0.99  
% 2.74/0.99  ------ QBF Options
% 2.74/0.99  
% 2.74/0.99  --qbf_mode                              false
% 2.74/0.99  --qbf_elim_univ                         false
% 2.74/0.99  --qbf_dom_inst                          none
% 2.74/0.99  --qbf_dom_pre_inst                      false
% 2.74/0.99  --qbf_sk_in                             false
% 2.74/0.99  --qbf_pred_elim                         true
% 2.74/0.99  --qbf_split                             512
% 2.74/0.99  
% 2.74/0.99  ------ BMC1 Options
% 2.74/0.99  
% 2.74/0.99  --bmc1_incremental                      false
% 2.74/0.99  --bmc1_axioms                           reachable_all
% 2.74/0.99  --bmc1_min_bound                        0
% 2.74/0.99  --bmc1_max_bound                        -1
% 2.74/0.99  --bmc1_max_bound_default                -1
% 2.74/0.99  --bmc1_symbol_reachability              true
% 2.74/0.99  --bmc1_property_lemmas                  false
% 2.74/0.99  --bmc1_k_induction                      false
% 2.74/0.99  --bmc1_non_equiv_states                 false
% 2.74/0.99  --bmc1_deadlock                         false
% 2.74/0.99  --bmc1_ucm                              false
% 2.74/0.99  --bmc1_add_unsat_core                   none
% 2.74/0.99  --bmc1_unsat_core_children              false
% 2.74/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.99  --bmc1_out_stat                         full
% 2.74/0.99  --bmc1_ground_init                      false
% 2.74/0.99  --bmc1_pre_inst_next_state              false
% 2.74/0.99  --bmc1_pre_inst_state                   false
% 2.74/0.99  --bmc1_pre_inst_reach_state             false
% 2.74/0.99  --bmc1_out_unsat_core                   false
% 2.74/0.99  --bmc1_aig_witness_out                  false
% 2.74/0.99  --bmc1_verbose                          false
% 2.74/0.99  --bmc1_dump_clauses_tptp                false
% 2.74/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.99  --bmc1_dump_file                        -
% 2.74/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.99  --bmc1_ucm_extend_mode                  1
% 2.74/0.99  --bmc1_ucm_init_mode                    2
% 2.74/0.99  --bmc1_ucm_cone_mode                    none
% 2.74/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.99  --bmc1_ucm_relax_model                  4
% 2.74/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.99  --bmc1_ucm_layered_model                none
% 2.74/0.99  --bmc1_ucm_max_lemma_size               10
% 2.74/0.99  
% 2.74/0.99  ------ AIG Options
% 2.74/0.99  
% 2.74/0.99  --aig_mode                              false
% 2.74/0.99  
% 2.74/0.99  ------ Instantiation Options
% 2.74/0.99  
% 2.74/0.99  --instantiation_flag                    true
% 2.74/0.99  --inst_sos_flag                         false
% 2.74/0.99  --inst_sos_phase                        true
% 2.74/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.99  --inst_lit_sel_side                     none
% 2.74/0.99  --inst_solver_per_active                1400
% 2.74/0.99  --inst_solver_calls_frac                1.
% 2.74/0.99  --inst_passive_queue_type               priority_queues
% 2.74/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.99  --inst_passive_queues_freq              [25;2]
% 2.74/0.99  --inst_dismatching                      true
% 2.74/0.99  --inst_eager_unprocessed_to_passive     true
% 2.74/0.99  --inst_prop_sim_given                   true
% 2.74/0.99  --inst_prop_sim_new                     false
% 2.74/0.99  --inst_subs_new                         false
% 2.74/0.99  --inst_eq_res_simp                      false
% 2.74/0.99  --inst_subs_given                       false
% 2.74/0.99  --inst_orphan_elimination               true
% 2.74/0.99  --inst_learning_loop_flag               true
% 2.74/0.99  --inst_learning_start                   3000
% 2.74/0.99  --inst_learning_factor                  2
% 2.74/0.99  --inst_start_prop_sim_after_learn       3
% 2.74/0.99  --inst_sel_renew                        solver
% 2.74/0.99  --inst_lit_activity_flag                true
% 2.74/0.99  --inst_restr_to_given                   false
% 2.74/0.99  --inst_activity_threshold               500
% 2.74/0.99  --inst_out_proof                        true
% 2.74/0.99  
% 2.74/0.99  ------ Resolution Options
% 2.74/0.99  
% 2.74/0.99  --resolution_flag                       false
% 2.74/0.99  --res_lit_sel                           adaptive
% 2.74/0.99  --res_lit_sel_side                      none
% 2.74/0.99  --res_ordering                          kbo
% 2.74/0.99  --res_to_prop_solver                    active
% 2.74/0.99  --res_prop_simpl_new                    false
% 2.74/0.99  --res_prop_simpl_given                  true
% 2.74/0.99  --res_passive_queue_type                priority_queues
% 2.74/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.99  --res_passive_queues_freq               [15;5]
% 2.74/0.99  --res_forward_subs                      full
% 2.74/0.99  --res_backward_subs                     full
% 2.74/0.99  --res_forward_subs_resolution           true
% 2.74/0.99  --res_backward_subs_resolution          true
% 2.74/0.99  --res_orphan_elimination                true
% 2.74/0.99  --res_time_limit                        2.
% 2.74/0.99  --res_out_proof                         true
% 2.74/0.99  
% 2.74/0.99  ------ Superposition Options
% 2.74/0.99  
% 2.74/0.99  --superposition_flag                    true
% 2.74/0.99  --sup_passive_queue_type                priority_queues
% 2.74/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.99  --demod_completeness_check              fast
% 2.74/0.99  --demod_use_ground                      true
% 2.74/0.99  --sup_to_prop_solver                    passive
% 2.74/0.99  --sup_prop_simpl_new                    true
% 2.74/0.99  --sup_prop_simpl_given                  true
% 2.74/0.99  --sup_fun_splitting                     false
% 2.74/0.99  --sup_smt_interval                      50000
% 2.74/0.99  
% 2.74/0.99  ------ Superposition Simplification Setup
% 2.74/0.99  
% 2.74/0.99  --sup_indices_passive                   []
% 2.74/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_full_bw                           [BwDemod]
% 2.74/0.99  --sup_immed_triv                        [TrivRules]
% 2.74/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_immed_bw_main                     []
% 2.74/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.99  
% 2.74/0.99  ------ Combination Options
% 2.74/0.99  
% 2.74/0.99  --comb_res_mult                         3
% 2.74/0.99  --comb_sup_mult                         2
% 2.74/0.99  --comb_inst_mult                        10
% 2.74/0.99  
% 2.74/0.99  ------ Debug Options
% 2.74/0.99  
% 2.74/0.99  --dbg_backtrace                         false
% 2.74/0.99  --dbg_dump_prop_clauses                 false
% 2.74/0.99  --dbg_dump_prop_clauses_file            -
% 2.74/0.99  --dbg_out_stat                          false
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  ------ Proving...
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  % SZS status Theorem for theBenchmark.p
% 2.74/0.99  
% 2.74/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.74/0.99  
% 2.74/0.99  fof(f12,axiom,(
% 2.74/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f28,plain,(
% 2.74/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.99    inference(ennf_transformation,[],[f12])).
% 2.74/0.99  
% 2.74/0.99  fof(f29,plain,(
% 2.74/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.99    inference(flattening,[],[f28])).
% 2.74/0.99  
% 2.74/0.99  fof(f35,plain,(
% 2.74/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.99    inference(nnf_transformation,[],[f29])).
% 2.74/0.99  
% 2.74/0.99  fof(f52,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f35])).
% 2.74/0.99  
% 2.74/0.99  fof(f14,conjecture,(
% 2.74/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f15,negated_conjecture,(
% 2.74/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.74/0.99    inference(negated_conjecture,[],[f14])).
% 2.74/0.99  
% 2.74/0.99  fof(f32,plain,(
% 2.74/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.74/0.99    inference(ennf_transformation,[],[f15])).
% 2.74/0.99  
% 2.74/0.99  fof(f33,plain,(
% 2.74/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.74/0.99    inference(flattening,[],[f32])).
% 2.74/0.99  
% 2.74/0.99  fof(f36,plain,(
% 2.74/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.74/0.99    introduced(choice_axiom,[])).
% 2.74/0.99  
% 2.74/0.99  fof(f37,plain,(
% 2.74/0.99    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36])).
% 2.74/0.99  
% 2.74/0.99  fof(f62,plain,(
% 2.74/0.99    v1_funct_2(sK2,sK0,sK1)),
% 2.74/0.99    inference(cnf_transformation,[],[f37])).
% 2.74/0.99  
% 2.74/0.99  fof(f63,plain,(
% 2.74/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.74/0.99    inference(cnf_transformation,[],[f37])).
% 2.74/0.99  
% 2.74/0.99  fof(f10,axiom,(
% 2.74/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f26,plain,(
% 2.74/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.99    inference(ennf_transformation,[],[f10])).
% 2.74/0.99  
% 2.74/0.99  fof(f50,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f26])).
% 2.74/0.99  
% 2.74/0.99  fof(f7,axiom,(
% 2.74/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f22,plain,(
% 2.74/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.74/0.99    inference(ennf_transformation,[],[f7])).
% 2.74/0.99  
% 2.74/0.99  fof(f23,plain,(
% 2.74/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.74/0.99    inference(flattening,[],[f22])).
% 2.74/0.99  
% 2.74/0.99  fof(f47,plain,(
% 2.74/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f23])).
% 2.74/0.99  
% 2.74/0.99  fof(f64,plain,(
% 2.74/0.99    v2_funct_1(sK2)),
% 2.74/0.99    inference(cnf_transformation,[],[f37])).
% 2.74/0.99  
% 2.74/0.99  fof(f61,plain,(
% 2.74/0.99    v1_funct_1(sK2)),
% 2.74/0.99    inference(cnf_transformation,[],[f37])).
% 2.74/0.99  
% 2.74/0.99  fof(f8,axiom,(
% 2.74/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f24,plain,(
% 2.74/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.99    inference(ennf_transformation,[],[f8])).
% 2.74/0.99  
% 2.74/0.99  fof(f48,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f24])).
% 2.74/0.99  
% 2.74/0.99  fof(f13,axiom,(
% 2.74/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f30,plain,(
% 2.74/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.74/0.99    inference(ennf_transformation,[],[f13])).
% 2.74/0.99  
% 2.74/0.99  fof(f31,plain,(
% 2.74/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.74/0.99    inference(flattening,[],[f30])).
% 2.74/0.99  
% 2.74/0.99  fof(f60,plain,(
% 2.74/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f31])).
% 2.74/0.99  
% 2.74/0.99  fof(f11,axiom,(
% 2.74/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f27,plain,(
% 2.74/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.99    inference(ennf_transformation,[],[f11])).
% 2.74/0.99  
% 2.74/0.99  fof(f51,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f27])).
% 2.74/0.99  
% 2.74/0.99  fof(f65,plain,(
% 2.74/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.74/0.99    inference(cnf_transformation,[],[f37])).
% 2.74/0.99  
% 2.74/0.99  fof(f46,plain,(
% 2.74/0.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f23])).
% 2.74/0.99  
% 2.74/0.99  fof(f6,axiom,(
% 2.74/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f20,plain,(
% 2.74/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.74/0.99    inference(ennf_transformation,[],[f6])).
% 2.74/0.99  
% 2.74/0.99  fof(f21,plain,(
% 2.74/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.74/0.99    inference(flattening,[],[f20])).
% 2.74/0.99  
% 2.74/0.99  fof(f44,plain,(
% 2.74/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f21])).
% 2.74/0.99  
% 2.74/0.99  fof(f45,plain,(
% 2.74/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f21])).
% 2.74/0.99  
% 2.74/0.99  fof(f59,plain,(
% 2.74/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f31])).
% 2.74/0.99  
% 2.74/0.99  fof(f66,plain,(
% 2.74/0.99    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.74/0.99    inference(cnf_transformation,[],[f37])).
% 2.74/0.99  
% 2.74/0.99  fof(f56,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f35])).
% 2.74/0.99  
% 2.74/0.99  fof(f69,plain,(
% 2.74/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.74/0.99    inference(equality_resolution,[],[f56])).
% 2.74/0.99  
% 2.74/0.99  fof(f1,axiom,(
% 2.74/0.99    v1_xboole_0(k1_xboole_0)),
% 2.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f38,plain,(
% 2.74/0.99    v1_xboole_0(k1_xboole_0)),
% 2.74/0.99    inference(cnf_transformation,[],[f1])).
% 2.74/0.99  
% 2.74/0.99  fof(f9,axiom,(
% 2.74/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f25,plain,(
% 2.74/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.74/0.99    inference(ennf_transformation,[],[f9])).
% 2.74/0.99  
% 2.74/0.99  fof(f49,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f25])).
% 2.74/0.99  
% 2.74/0.99  fof(f3,axiom,(
% 2.74/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f17,plain,(
% 2.74/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.74/0.99    inference(ennf_transformation,[],[f3])).
% 2.74/0.99  
% 2.74/0.99  fof(f40,plain,(
% 2.74/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f17])).
% 2.74/0.99  
% 2.74/0.99  fof(f5,axiom,(
% 2.74/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f19,plain,(
% 2.74/0.99    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.74/0.99    inference(ennf_transformation,[],[f5])).
% 2.74/0.99  
% 2.74/0.99  fof(f34,plain,(
% 2.74/0.99    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.74/0.99    inference(nnf_transformation,[],[f19])).
% 2.74/0.99  
% 2.74/0.99  fof(f43,plain,(
% 2.74/0.99    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f34])).
% 2.74/0.99  
% 2.74/0.99  fof(f2,axiom,(
% 2.74/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f39,plain,(
% 2.74/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f2])).
% 2.74/0.99  
% 2.74/0.99  fof(f4,axiom,(
% 2.74/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.74/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f16,plain,(
% 2.74/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.74/0.99    inference(unused_predicate_definition_removal,[],[f4])).
% 2.74/0.99  
% 2.74/0.99  fof(f18,plain,(
% 2.74/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 2.74/0.99    inference(ennf_transformation,[],[f16])).
% 2.74/0.99  
% 2.74/0.99  fof(f41,plain,(
% 2.74/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f18])).
% 2.74/0.99  
% 2.74/0.99  fof(f55,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f35])).
% 2.74/0.99  
% 2.74/0.99  fof(f70,plain,(
% 2.74/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.74/0.99    inference(equality_resolution,[],[f55])).
% 2.74/0.99  
% 2.74/0.99  cnf(c_19,plain,
% 2.74/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.74/0.99      | k1_xboole_0 = X2 ),
% 2.74/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_27,negated_conjecture,
% 2.74/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.74/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1076,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.74/0.99      | sK0 != X1
% 2.74/0.99      | sK1 != X2
% 2.74/0.99      | sK2 != X0
% 2.74/0.99      | k1_xboole_0 = X2 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1077,plain,
% 2.74/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.74/0.99      | k1_relset_1(sK0,sK1,sK2) = sK0
% 2.74/0.99      | k1_xboole_0 = sK1 ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_1076]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_26,negated_conjecture,
% 2.74/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.74/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1079,plain,
% 2.74/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_1077,c_26]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1352,plain,
% 2.74/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_1079]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1365,negated_conjecture,
% 2.74/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_26]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1860,plain,
% 2.74/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1365]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_12,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1369,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.74/0.99      | k1_relset_1(X1_46,X2_46,X0_46) = k1_relat_1(X0_46) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1857,plain,
% 2.74/0.99      ( k1_relset_1(X0_46,X1_46,X2_46) = k1_relat_1(X2_46)
% 2.74/0.99      | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1369]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2626,plain,
% 2.74/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1860,c_1857]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2791,plain,
% 2.74/0.99      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1352,c_2626]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_8,plain,
% 2.74/0.99      ( ~ v2_funct_1(X0)
% 2.74/0.99      | ~ v1_funct_1(X0)
% 2.74/0.99      | ~ v1_relat_1(X0)
% 2.74/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_25,negated_conjecture,
% 2.74/0.99      ( v2_funct_1(sK2) ),
% 2.74/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_338,plain,
% 2.74/0.99      ( ~ v1_funct_1(X0)
% 2.74/0.99      | ~ v1_relat_1(X0)
% 2.74/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.74/0.99      | sK2 != X0 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_339,plain,
% 2.74/0.99      ( ~ v1_funct_1(sK2)
% 2.74/0.99      | ~ v1_relat_1(sK2)
% 2.74/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_338]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_28,negated_conjecture,
% 2.74/0.99      ( v1_funct_1(sK2) ),
% 2.74/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_341,plain,
% 2.74/0.99      ( ~ v1_relat_1(sK2)
% 2.74/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_339,c_28]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1361,plain,
% 2.74/0.99      ( ~ v1_relat_1(sK2)
% 2.74/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_341]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1864,plain,
% 2.74/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.74/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1361]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_10,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | v1_relat_1(X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1371,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.74/0.99      | v1_relat_1(X0_46) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2104,plain,
% 2.74/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.74/0.99      | v1_relat_1(sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1371]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2131,plain,
% 2.74/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_1864,c_26,c_1361,c_2104]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_20,plain,
% 2.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.74/0.99      | ~ v1_funct_1(X0)
% 2.74/0.99      | ~ v1_relat_1(X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1367,plain,
% 2.74/0.99      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_46),k2_relat_1(X0_46))))
% 2.74/0.99      | ~ v1_funct_1(X0_46)
% 2.74/0.99      | ~ v1_relat_1(X0_46) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1859,plain,
% 2.74/0.99      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_46),k2_relat_1(X0_46)))) = iProver_top
% 2.74/0.99      | v1_funct_1(X0_46) != iProver_top
% 2.74/0.99      | v1_relat_1(X0_46) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1367]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3025,plain,
% 2.74/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 2.74/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.74/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2131,c_1859]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_13,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1368,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.74/0.99      | k2_relset_1(X1_46,X2_46,X0_46) = k2_relat_1(X0_46) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1858,plain,
% 2.74/0.99      ( k2_relset_1(X0_46,X1_46,X2_46) = k2_relat_1(X2_46)
% 2.74/0.99      | m1_subset_1(X2_46,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1368]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2710,plain,
% 2.74/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1860,c_1858]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_24,negated_conjecture,
% 2.74/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.74/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1366,negated_conjecture,
% 2.74/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2715,plain,
% 2.74/0.99      ( k2_relat_1(sK2) = sK1 ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_2710,c_1366]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_9,plain,
% 2.74/0.99      ( ~ v2_funct_1(X0)
% 2.74/0.99      | ~ v1_funct_1(X0)
% 2.74/0.99      | ~ v1_relat_1(X0)
% 2.74/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_324,plain,
% 2.74/0.99      ( ~ v1_funct_1(X0)
% 2.74/0.99      | ~ v1_relat_1(X0)
% 2.74/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.74/0.99      | sK2 != X0 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_325,plain,
% 2.74/0.99      ( ~ v1_funct_1(sK2)
% 2.74/0.99      | ~ v1_relat_1(sK2)
% 2.74/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_324]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_327,plain,
% 2.74/0.99      ( ~ v1_relat_1(sK2)
% 2.74/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_325,c_28]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1362,plain,
% 2.74/0.99      ( ~ v1_relat_1(sK2)
% 2.74/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_327]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1863,plain,
% 2.74/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.74/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1362]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2127,plain,
% 2.74/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_1863,c_26,c_1362,c_2104]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2721,plain,
% 2.74/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_2715,c_2127]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3053,plain,
% 2.74/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 2.74/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.74/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_3025,c_2721]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_29,plain,
% 2.74/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_31,plain,
% 2.74/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_7,plain,
% 2.74/0.99      ( ~ v1_funct_1(X0)
% 2.74/0.99      | ~ v1_relat_1(X0)
% 2.74/0.99      | v1_relat_1(k2_funct_1(X0)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1372,plain,
% 2.74/0.99      ( ~ v1_funct_1(X0_46)
% 2.74/0.99      | ~ v1_relat_1(X0_46)
% 2.74/0.99      | v1_relat_1(k2_funct_1(X0_46)) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2094,plain,
% 2.74/0.99      ( ~ v1_funct_1(sK2)
% 2.74/0.99      | v1_relat_1(k2_funct_1(sK2))
% 2.74/0.99      | ~ v1_relat_1(sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1372]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2095,plain,
% 2.74/0.99      ( v1_funct_1(sK2) != iProver_top
% 2.74/0.99      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.74/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_2094]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6,plain,
% 2.74/0.99      ( ~ v1_funct_1(X0)
% 2.74/0.99      | v1_funct_1(k2_funct_1(X0))
% 2.74/0.99      | ~ v1_relat_1(X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1373,plain,
% 2.74/0.99      ( ~ v1_funct_1(X0_46)
% 2.74/0.99      | v1_funct_1(k2_funct_1(X0_46))
% 2.74/0.99      | ~ v1_relat_1(X0_46) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2097,plain,
% 2.74/0.99      ( v1_funct_1(k2_funct_1(sK2))
% 2.74/0.99      | ~ v1_funct_1(sK2)
% 2.74/0.99      | ~ v1_relat_1(sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1373]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2098,plain,
% 2.74/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.74/0.99      | v1_funct_1(sK2) != iProver_top
% 2.74/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_2097]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2105,plain,
% 2.74/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.74/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_2104]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3583,plain,
% 2.74/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_3053,c_29,c_31,c_2095,c_2098,c_2105]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3592,plain,
% 2.74/0.99      ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_3583,c_1857]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3594,plain,
% 2.74/0.99      ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = sK1 ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_3592,c_2721]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3733,plain,
% 2.74/0.99      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1 | sK1 = k1_xboole_0 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2791,c_3594]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_21,plain,
% 2.74/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.74/0.99      | ~ v1_funct_1(X0)
% 2.74/0.99      | ~ v1_relat_1(X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_23,negated_conjecture,
% 2.74/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.74/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.74/0.99      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1087,plain,
% 2.74/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.74/0.99      | ~ v1_funct_1(X0)
% 2.74/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.74/0.99      | ~ v1_relat_1(X0)
% 2.74/0.99      | k2_funct_1(sK2) != X0
% 2.74/0.99      | k2_relat_1(X0) != sK0
% 2.74/0.99      | k1_relat_1(X0) != sK1 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_23]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1088,plain,
% 2.74/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.74/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.74/0.99      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.74/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.74/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_1087]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1100,plain,
% 2.74/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.74/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.74/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.74/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.74/0.99      inference(forward_subsumption_resolution,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_1088,c_10]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1351,plain,
% 2.74/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.74/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.74/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.74/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_1100]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1873,plain,
% 2.74/0.99      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.74/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.74/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.74/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1351]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1447,plain,
% 2.74/0.99      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.74/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.74/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.74/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1351]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2511,plain,
% 2.74/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.74/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.74/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_1873,c_29,c_31,c_1447,c_2098,c_2105]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2512,plain,
% 2.74/0.99      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.74/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.74/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.74/0.99      inference(renaming,[status(thm)],[c_2511]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2515,plain,
% 2.74/0.99      ( k2_relat_1(sK2) != sK1
% 2.74/0.99      | k1_relat_1(sK2) != sK0
% 2.74/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_2512,c_2127,c_2131]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2719,plain,
% 2.74/0.99      ( k1_relat_1(sK2) != sK0
% 2.74/0.99      | sK1 != sK1
% 2.74/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_2715,c_2515]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2728,plain,
% 2.74/0.99      ( k1_relat_1(sK2) != sK0
% 2.74/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.74/0.99      inference(equality_resolution_simp,[status(thm)],[c_2719]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2966,plain,
% 2.74/0.99      ( sK1 = k1_xboole_0
% 2.74/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2791,c_2728]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3588,plain,
% 2.74/0.99      ( sK1 = k1_xboole_0
% 2.74/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2791,c_3583]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3776,plain,
% 2.74/0.99      ( sK1 = k1_xboole_0 ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_3733,c_2966,c_3588]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_15,plain,
% 2.74/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.74/0.99      | k1_xboole_0 = X1
% 2.74/0.99      | k1_xboole_0 = X0 ),
% 2.74/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_961,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.74/0.99      | sK0 != X1
% 2.74/0.99      | sK1 != k1_xboole_0
% 2.74/0.99      | sK2 != X0
% 2.74/0.99      | k1_xboole_0 = X0
% 2.74/0.99      | k1_xboole_0 = X1 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_962,plain,
% 2.74/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 2.74/0.99      | sK1 != k1_xboole_0
% 2.74/0.99      | k1_xboole_0 = sK0
% 2.74/0.99      | k1_xboole_0 = sK2 ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_961]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1358,plain,
% 2.74/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 2.74/0.99      | sK1 != k1_xboole_0
% 2.74/0.99      | k1_xboole_0 = sK0
% 2.74/0.99      | k1_xboole_0 = sK2 ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_962]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1867,plain,
% 2.74/0.99      ( sK1 != k1_xboole_0
% 2.74/0.99      | k1_xboole_0 = sK0
% 2.74/0.99      | k1_xboole_0 = sK2
% 2.74/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1358]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3792,plain,
% 2.74/0.99      ( sK0 = k1_xboole_0
% 2.74/0.99      | sK2 = k1_xboole_0
% 2.74/0.99      | k1_xboole_0 != k1_xboole_0
% 2.74/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_3776,c_1867]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3828,plain,
% 2.74/0.99      ( sK0 = k1_xboole_0
% 2.74/0.99      | sK2 = k1_xboole_0
% 2.74/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 2.74/0.99      inference(equality_resolution_simp,[status(thm)],[c_3792]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3799,plain,
% 2.74/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_3776,c_1860]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3832,plain,
% 2.74/0.99      ( sK0 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.74/0.99      inference(forward_subsumption_resolution,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_3828,c_3799]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_0,plain,
% 2.74/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_96,plain,
% 2.74/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_11,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.99      | ~ v1_xboole_0(X1)
% 2.74/0.99      | v1_xboole_0(X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1370,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46)))
% 2.74/0.99      | ~ v1_xboole_0(X1_46)
% 2.74/0.99      | v1_xboole_0(X0_46) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2392,plain,
% 2.74/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 2.74/0.99      | ~ v1_xboole_0(X0_46)
% 2.74/0.99      | v1_xboole_0(sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1370]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2393,plain,
% 2.74/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
% 2.74/0.99      | v1_xboole_0(X0_46) != iProver_top
% 2.74/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_2392]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2395,plain,
% 2.74/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 2.74/0.99      | v1_xboole_0(sK2) = iProver_top
% 2.74/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_2393]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2,plain,
% 2.74/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 2.74/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1376,plain,
% 2.74/0.99      ( ~ v1_xboole_0(X0_46) | ~ v1_xboole_0(X1_46) | X0_46 = X1_46 ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2439,plain,
% 2.74/0.99      ( ~ v1_xboole_0(X0_46) | ~ v1_xboole_0(sK2) | sK2 = X0_46 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1376]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2440,plain,
% 2.74/0.99      ( sK2 = X0_46
% 2.74/0.99      | v1_xboole_0(X0_46) != iProver_top
% 2.74/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_2439]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2442,plain,
% 2.74/0.99      ( sK2 = k1_xboole_0
% 2.74/0.99      | v1_xboole_0(sK2) != iProver_top
% 2.74/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_2440]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3024,plain,
% 2.74/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top
% 2.74/0.99      | v1_funct_1(sK2) != iProver_top
% 2.74/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2715,c_1859]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3390,plain,
% 2.74/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_3024,c_29,c_31,c_2105]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3784,plain,
% 2.74/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) = iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_3776,c_3390]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4,plain,
% 2.74/0.99      ( ~ v1_relat_1(X0)
% 2.74/0.99      | k2_relat_1(X0) != k1_xboole_0
% 2.74/0.99      | k1_relat_1(X0) = k1_xboole_0 ),
% 2.74/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1375,plain,
% 2.74/0.99      ( ~ v1_relat_1(X0_46)
% 2.74/0.99      | k2_relat_1(X0_46) != k1_xboole_0
% 2.74/0.99      | k1_relat_1(X0_46) = k1_xboole_0 ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1851,plain,
% 2.74/0.99      ( k2_relat_1(X0_46) != k1_xboole_0
% 2.74/0.99      | k1_relat_1(X0_46) = k1_xboole_0
% 2.74/0.99      | v1_relat_1(X0_46) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1375]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2734,plain,
% 2.74/0.99      ( k1_relat_1(sK2) = k1_xboole_0
% 2.74/0.99      | sK1 != k1_xboole_0
% 2.74/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2715,c_1851]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2851,plain,
% 2.74/0.99      ( sK1 != k1_xboole_0 | k1_relat_1(sK2) = k1_xboole_0 ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_2734,c_31,c_2105]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2852,plain,
% 2.74/0.99      ( k1_relat_1(sK2) = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 2.74/0.99      inference(renaming,[status(thm)],[c_2851]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3787,plain,
% 2.74/0.99      ( k1_relat_1(sK2) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_3776,c_2852]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3841,plain,
% 2.74/0.99      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 2.74/0.99      inference(equality_resolution_simp,[status(thm)],[c_3787]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3852,plain,
% 2.74/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_3784,c_3841]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4168,plain,
% 2.74/0.99      ( sK2 = k1_xboole_0 ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_3832,c_96,c_2395,c_2442,c_3852]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3791,plain,
% 2.74/0.99      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_3776,c_2715]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4174,plain,
% 2.74/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_4168,c_3791]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4305,plain,
% 2.74/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 2.74/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_4174,c_1851]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1379,plain,( X0_46 = X0_46 ),theory(equality) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1406,plain,
% 2.74/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1379]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1412,plain,
% 2.74/0.99      ( ~ v1_relat_1(k1_xboole_0)
% 2.74/0.99      | k2_relat_1(k1_xboole_0) != k1_xboole_0
% 2.74/0.99      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1375]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2107,plain,
% 2.74/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 2.74/0.99      | v1_relat_1(k1_xboole_0) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1371]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1,plain,
% 2.74/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3,plain,
% 2.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.74/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_309,plain,
% 2.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | X1 != X2 | k1_xboole_0 != X0 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_3]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_310,plain,
% 2.74/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_309]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1363,plain,
% 2.74/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_48)) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_310]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2108,plain,
% 2.74/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1363]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2240,plain,
% 2.74/0.99      ( ~ v1_xboole_0(X0_46) | ~ v1_xboole_0(sK2) | X0_46 = sK2 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1376]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2241,plain,
% 2.74/0.99      ( X0_46 = sK2
% 2.74/0.99      | v1_xboole_0(X0_46) != iProver_top
% 2.74/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_2240]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2243,plain,
% 2.74/0.99      ( k1_xboole_0 = sK2
% 2.74/0.99      | v1_xboole_0(sK2) != iProver_top
% 2.74/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_2241]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2321,plain,
% 2.74/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 2.74/0.99      | k1_relat_1(sK2) != k1_xboole_0
% 2.74/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2131,c_1851]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2322,plain,
% 2.74/0.99      ( k2_relat_1(sK2) = k1_xboole_0
% 2.74/0.99      | k1_relat_1(sK2) != k1_xboole_0
% 2.74/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_2321,c_2127]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1382,plain,
% 2.74/0.99      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 2.74/0.99      theory(equality) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2578,plain,
% 2.74/0.99      ( k2_relat_1(sK2) != X0_46
% 2.74/0.99      | k1_xboole_0 != X0_46
% 2.74/0.99      | k1_xboole_0 = k2_relat_1(sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1382]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2579,plain,
% 2.74/0.99      ( k2_relat_1(sK2) != k1_xboole_0
% 2.74/0.99      | k1_xboole_0 = k2_relat_1(sK2)
% 2.74/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_2578]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2419,plain,
% 2.74/0.99      ( k2_relat_1(X0_46) != X1_46
% 2.74/0.99      | k2_relat_1(X0_46) = k1_xboole_0
% 2.74/0.99      | k1_xboole_0 != X1_46 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1382]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2780,plain,
% 2.74/0.99      ( k2_relat_1(X0_46) != k2_relat_1(X1_46)
% 2.74/0.99      | k2_relat_1(X0_46) = k1_xboole_0
% 2.74/0.99      | k1_xboole_0 != k2_relat_1(X1_46) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_2419]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3428,plain,
% 2.74/0.99      ( k2_relat_1(X0_46) != k2_relat_1(sK2)
% 2.74/0.99      | k2_relat_1(X0_46) = k1_xboole_0
% 2.74/0.99      | k1_xboole_0 != k2_relat_1(sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_2780]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3429,plain,
% 2.74/0.99      ( k2_relat_1(k1_xboole_0) != k2_relat_1(sK2)
% 2.74/0.99      | k2_relat_1(k1_xboole_0) = k1_xboole_0
% 2.74/0.99      | k1_xboole_0 != k2_relat_1(sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_3428]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1387,plain,
% 2.74/0.99      ( X0_46 != X1_46 | k2_relat_1(X0_46) = k2_relat_1(X1_46) ),
% 2.74/0.99      theory(equality) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3650,plain,
% 2.74/0.99      ( X0_46 != sK2 | k2_relat_1(X0_46) = k2_relat_1(sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1387]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3652,plain,
% 2.74/0.99      ( k2_relat_1(k1_xboole_0) = k2_relat_1(sK2) | k1_xboole_0 != sK2 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_3650]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4320,plain,
% 2.74/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_4305,c_29,c_31,c_96,c_1406,c_1412,c_2095,c_2105,
% 2.74/0.99                 c_2107,c_2108,c_2243,c_2322,c_2395,c_2579,c_2734,c_2966,
% 2.74/0.99                 c_3429,c_3588,c_3652,c_3852]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1862,plain,
% 2.74/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_48)) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1363]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2627,plain,
% 2.74/0.99      ( k1_relset_1(X0_46,X1_46,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1862,c_1857]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4323,plain,
% 2.74/0.99      ( k1_relset_1(X0_46,X1_46,k1_xboole_0) = k1_xboole_0 ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_4320,c_2627]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_16,plain,
% 2.74/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.74/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.74/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.74/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1004,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.74/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.74/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.74/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.74/0.99      | k2_funct_1(sK2) != X0
% 2.74/0.99      | sK0 != X1
% 2.74/0.99      | sK1 != k1_xboole_0 ),
% 2.74/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1005,plain,
% 2.74/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.74/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.74/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.74/0.99      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.74/0.99      | sK1 != k1_xboole_0 ),
% 2.74/0.99      inference(unflattening,[status(thm)],[c_1004]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1356,plain,
% 2.74/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.74/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.74/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.74/0.99      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.74/0.99      | sK1 != k1_xboole_0 ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_1005]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1869,plain,
% 2.74/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.74/0.99      | sK1 != k1_xboole_0
% 2.74/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.74/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.74/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1356]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1441,plain,
% 2.74/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.74/0.99      | sK1 != k1_xboole_0
% 2.74/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.74/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.74/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1356]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2468,plain,
% 2.74/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.74/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.74/0.99      | sK1 != k1_xboole_0
% 2.74/0.99      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_1869,c_29,c_31,c_1441,c_2098,c_2105]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2469,plain,
% 2.74/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.74/0.99      | sK1 != k1_xboole_0
% 2.74/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.74/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.74/0.99      inference(renaming,[status(thm)],[c_2468]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3793,plain,
% 2.74/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.74/0.99      | k1_xboole_0 != k1_xboole_0
% 2.74/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_3776,c_2469]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3823,plain,
% 2.74/0.99      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.74/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.74/0.99      inference(equality_resolution_simp,[status(thm)],[c_3793]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1856,plain,
% 2.74/0.99      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X1_46,X2_46))) != iProver_top
% 2.74/0.99      | v1_xboole_0(X1_46) != iProver_top
% 2.74/0.99      | v1_xboole_0(X0_46) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1370]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3589,plain,
% 2.74/0.99      ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top
% 2.74/0.99      | v1_xboole_0(sK1) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_3583,c_1856]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2185,plain,
% 2.74/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
% 2.74/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.74/0.99      | ~ v1_relat_1(k2_funct_1(sK2)) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1367]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2197,plain,
% 2.74/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 2.74/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.74/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_2185]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1383,plain,
% 2.74/0.99      ( ~ v1_xboole_0(X0_46) | v1_xboole_0(X1_46) | X1_46 != X0_46 ),
% 2.74/0.99      theory(equality) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2526,plain,
% 2.74/0.99      ( ~ v1_xboole_0(X0_46)
% 2.74/0.99      | v1_xboole_0(k1_relat_1(X1_46))
% 2.74/0.99      | k1_relat_1(X1_46) != X0_46 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1383]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2924,plain,
% 2.74/0.99      ( ~ v1_xboole_0(k2_relat_1(sK2))
% 2.74/0.99      | v1_xboole_0(k1_relat_1(k2_funct_1(sK2)))
% 2.74/0.99      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_2526]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2925,plain,
% 2.74/0.99      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.74/0.99      | v1_xboole_0(k2_relat_1(sK2)) != iProver_top
% 2.74/0.99      | v1_xboole_0(k1_relat_1(k2_funct_1(sK2))) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_2924]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2554,plain,
% 2.74/0.99      ( ~ v1_xboole_0(X0_46)
% 2.74/0.99      | v1_xboole_0(k2_relat_1(X1_46))
% 2.74/0.99      | k2_relat_1(X1_46) != X0_46 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1383]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3217,plain,
% 2.74/0.99      ( v1_xboole_0(k2_relat_1(sK2))
% 2.74/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.74/0.99      | k2_relat_1(sK2) != k1_xboole_0 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_2554]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3218,plain,
% 2.74/0.99      ( k2_relat_1(sK2) != k1_xboole_0
% 2.74/0.99      | v1_xboole_0(k2_relat_1(sK2)) = iProver_top
% 2.74/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_3217]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2669,plain,
% 2.74/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 2.74/0.99      | ~ v1_xboole_0(X0_46)
% 2.74/0.99      | v1_xboole_0(k2_funct_1(sK2)) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1370]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3256,plain,
% 2.74/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
% 2.74/0.99      | v1_xboole_0(k2_funct_1(sK2))
% 2.74/0.99      | ~ v1_xboole_0(k1_relat_1(k2_funct_1(sK2))) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_2669]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3257,plain,
% 2.74/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) != iProver_top
% 2.74/0.99      | v1_xboole_0(k2_funct_1(sK2)) = iProver_top
% 2.74/0.99      | v1_xboole_0(k1_relat_1(k2_funct_1(sK2))) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_3256]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3720,plain,
% 2.74/0.99      ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_3589,c_29,c_26,c_31,c_96,c_1362,c_2095,c_2098,c_2104,
% 2.74/0.99                 c_2105,c_2197,c_2322,c_2734,c_2925,c_2966,c_3218,c_3257,
% 2.74/0.99                 c_3588]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1377,plain,
% 2.74/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.74/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1849,plain,
% 2.74/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1377]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1850,plain,
% 2.74/0.99      ( X0_46 = X1_46
% 2.74/0.99      | v1_xboole_0(X1_46) != iProver_top
% 2.74/0.99      | v1_xboole_0(X0_46) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1376]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2232,plain,
% 2.74/0.99      ( k1_xboole_0 = X0_46 | v1_xboole_0(X0_46) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1849,c_1850]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3726,plain,
% 2.74/0.99      ( k2_funct_1(sK2) = k1_xboole_0 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_3720,c_2232]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4740,plain,
% 2.74/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_3726,c_4168]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5054,plain,
% 2.74/0.99      ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0
% 2.74/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_3823,c_4168,c_4740]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5057,plain,
% 2.74/0.99      ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0 ),
% 2.74/0.99      inference(forward_subsumption_resolution,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_5054,c_1862]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5308,plain,
% 2.74/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_4323,c_5057]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(contradiction,plain,
% 2.74/0.99      ( $false ),
% 2.74/0.99      inference(minisat,[status(thm)],[c_5308,c_1406]) ).
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.74/0.99  
% 2.74/0.99  ------                               Statistics
% 2.74/0.99  
% 2.74/0.99  ------ General
% 2.74/0.99  
% 2.74/0.99  abstr_ref_over_cycles:                  0
% 2.74/0.99  abstr_ref_under_cycles:                 0
% 2.74/0.99  gc_basic_clause_elim:                   0
% 2.74/0.99  forced_gc_time:                         0
% 2.74/0.99  parsing_time:                           0.009
% 2.74/0.99  unif_index_cands_time:                  0.
% 2.74/0.99  unif_index_add_time:                    0.
% 2.74/0.99  orderings_time:                         0.
% 2.74/0.99  out_proof_time:                         0.012
% 2.74/0.99  total_time:                             0.195
% 2.74/0.99  num_of_symbols:                         49
% 2.74/0.99  num_of_terms:                           3060
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing
% 2.74/0.99  
% 2.74/0.99  num_of_splits:                          0
% 2.74/0.99  num_of_split_atoms:                     0
% 2.74/0.99  num_of_reused_defs:                     0
% 2.74/0.99  num_eq_ax_congr_red:                    3
% 2.74/0.99  num_of_sem_filtered_clauses:            1
% 2.74/0.99  num_of_subtypes:                        3
% 2.74/0.99  monotx_restored_types:                  1
% 2.74/0.99  sat_num_of_epr_types:                   0
% 2.74/0.99  sat_num_of_non_cyclic_types:            0
% 2.74/0.99  sat_guarded_non_collapsed_types:        1
% 2.74/0.99  num_pure_diseq_elim:                    0
% 2.74/0.99  simp_replaced_by:                       0
% 2.74/0.99  res_preprocessed:                       143
% 2.74/0.99  prep_upred:                             0
% 2.74/0.99  prep_unflattend:                        73
% 2.74/0.99  smt_new_axioms:                         0
% 2.74/0.99  pred_elim_cands:                        4
% 2.74/0.99  pred_elim:                              3
% 2.74/0.99  pred_elim_cl:                           0
% 2.74/0.99  pred_elim_cycles:                       6
% 2.74/0.99  merged_defs:                            0
% 2.74/0.99  merged_defs_ncl:                        0
% 2.74/0.99  bin_hyper_res:                          0
% 2.74/0.99  prep_cycles:                            4
% 2.74/0.99  pred_elim_time:                         0.02
% 2.74/0.99  splitting_time:                         0.
% 2.74/0.99  sem_filter_time:                        0.
% 2.74/0.99  monotx_time:                            0.001
% 2.74/0.99  subtype_inf_time:                       0.002
% 2.74/0.99  
% 2.74/0.99  ------ Problem properties
% 2.74/0.99  
% 2.74/0.99  clauses:                                28
% 2.74/0.99  conjectures:                            3
% 2.74/0.99  epr:                                    3
% 2.74/0.99  horn:                                   24
% 2.74/0.99  ground:                                 14
% 2.74/0.99  unary:                                  5
% 2.74/0.99  binary:                                 6
% 2.74/0.99  lits:                                   80
% 2.74/0.99  lits_eq:                                35
% 2.74/0.99  fd_pure:                                0
% 2.74/0.99  fd_pseudo:                              0
% 2.74/0.99  fd_cond:                                1
% 2.74/0.99  fd_pseudo_cond:                         1
% 2.74/0.99  ac_symbols:                             0
% 2.74/0.99  
% 2.74/0.99  ------ Propositional Solver
% 2.74/0.99  
% 2.74/0.99  prop_solver_calls:                      28
% 2.74/0.99  prop_fast_solver_calls:                 1263
% 2.74/0.99  smt_solver_calls:                       0
% 2.74/0.99  smt_fast_solver_calls:                  0
% 2.74/0.99  prop_num_of_clauses:                    1575
% 2.74/0.99  prop_preprocess_simplified:             5105
% 2.74/0.99  prop_fo_subsumed:                       51
% 2.74/0.99  prop_solver_time:                       0.
% 2.74/0.99  smt_solver_time:                        0.
% 2.74/0.99  smt_fast_solver_time:                   0.
% 2.74/0.99  prop_fast_solver_time:                  0.
% 2.74/0.99  prop_unsat_core_time:                   0.
% 2.74/0.99  
% 2.74/0.99  ------ QBF
% 2.74/0.99  
% 2.74/0.99  qbf_q_res:                              0
% 2.74/0.99  qbf_num_tautologies:                    0
% 2.74/0.99  qbf_prep_cycles:                        0
% 2.74/0.99  
% 2.74/0.99  ------ BMC1
% 2.74/0.99  
% 2.74/0.99  bmc1_current_bound:                     -1
% 2.74/0.99  bmc1_last_solved_bound:                 -1
% 2.74/0.99  bmc1_unsat_core_size:                   -1
% 2.74/0.99  bmc1_unsat_core_parents_size:           -1
% 2.74/0.99  bmc1_merge_next_fun:                    0
% 2.74/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.74/0.99  
% 2.74/0.99  ------ Instantiation
% 2.74/0.99  
% 2.74/0.99  inst_num_of_clauses:                    511
% 2.74/0.99  inst_num_in_passive:                    111
% 2.74/0.99  inst_num_in_active:                     262
% 2.74/0.99  inst_num_in_unprocessed:                138
% 2.74/0.99  inst_num_of_loops:                      440
% 2.74/0.99  inst_num_of_learning_restarts:          0
% 2.74/0.99  inst_num_moves_active_passive:          175
% 2.74/0.99  inst_lit_activity:                      0
% 2.74/0.99  inst_lit_activity_moves:                0
% 2.74/0.99  inst_num_tautologies:                   0
% 2.74/0.99  inst_num_prop_implied:                  0
% 2.74/0.99  inst_num_existing_simplified:           0
% 2.74/0.99  inst_num_eq_res_simplified:             0
% 2.74/0.99  inst_num_child_elim:                    0
% 2.74/0.99  inst_num_of_dismatching_blockings:      136
% 2.74/0.99  inst_num_of_non_proper_insts:           609
% 2.74/0.99  inst_num_of_duplicates:                 0
% 2.74/0.99  inst_inst_num_from_inst_to_res:         0
% 2.74/0.99  inst_dismatching_checking_time:         0.
% 2.74/0.99  
% 2.74/0.99  ------ Resolution
% 2.74/0.99  
% 2.74/0.99  res_num_of_clauses:                     0
% 2.74/0.99  res_num_in_passive:                     0
% 2.74/0.99  res_num_in_active:                      0
% 2.74/0.99  res_num_of_loops:                       147
% 2.74/0.99  res_forward_subset_subsumed:            30
% 2.74/0.99  res_backward_subset_subsumed:           4
% 2.74/0.99  res_forward_subsumed:                   0
% 2.74/0.99  res_backward_subsumed:                  0
% 2.74/0.99  res_forward_subsumption_resolution:     3
% 2.74/0.99  res_backward_subsumption_resolution:    1
% 2.74/0.99  res_clause_to_clause_subsumption:       271
% 2.74/0.99  res_orphan_elimination:                 0
% 2.74/0.99  res_tautology_del:                      100
% 2.74/0.99  res_num_eq_res_simplified:              0
% 2.74/0.99  res_num_sel_changes:                    0
% 2.74/0.99  res_moves_from_active_to_pass:          0
% 2.74/0.99  
% 2.74/0.99  ------ Superposition
% 2.74/0.99  
% 2.74/0.99  sup_time_total:                         0.
% 2.74/0.99  sup_time_generating:                    0.
% 2.74/0.99  sup_time_sim_full:                      0.
% 2.74/0.99  sup_time_sim_immed:                     0.
% 2.74/0.99  
% 2.74/0.99  sup_num_of_clauses:                     58
% 2.74/0.99  sup_num_in_active:                      40
% 2.74/0.99  sup_num_in_passive:                     18
% 2.74/0.99  sup_num_of_loops:                       87
% 2.74/0.99  sup_fw_superposition:                   56
% 2.74/0.99  sup_bw_superposition:                   48
% 2.74/0.99  sup_immediate_simplified:               66
% 2.74/0.99  sup_given_eliminated:                   1
% 2.74/0.99  comparisons_done:                       0
% 2.74/0.99  comparisons_avoided:                    5
% 2.74/0.99  
% 2.74/0.99  ------ Simplifications
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  sim_fw_subset_subsumed:                 19
% 2.74/0.99  sim_bw_subset_subsumed:                 7
% 2.74/0.99  sim_fw_subsumed:                        7
% 2.74/0.99  sim_bw_subsumed:                        2
% 2.74/0.99  sim_fw_subsumption_res:                 2
% 2.74/0.99  sim_bw_subsumption_res:                 1
% 2.74/0.99  sim_tautology_del:                      4
% 2.74/0.99  sim_eq_tautology_del:                   15
% 2.74/0.99  sim_eq_res_simp:                        4
% 2.74/0.99  sim_fw_demodulated:                     9
% 2.74/0.99  sim_bw_demodulated:                     47
% 2.74/0.99  sim_light_normalised:                   45
% 2.74/0.99  sim_joinable_taut:                      0
% 2.74/0.99  sim_joinable_simp:                      0
% 2.74/0.99  sim_ac_normalised:                      0
% 2.74/0.99  sim_smt_subsumption:                    0
% 2.74/0.99  
%------------------------------------------------------------------------------
