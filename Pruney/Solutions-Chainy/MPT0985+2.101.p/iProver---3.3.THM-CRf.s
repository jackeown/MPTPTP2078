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
% DateTime   : Thu Dec  3 12:02:40 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :  233 (18149 expanded)
%              Number of clauses        :  150 (5588 expanded)
%              Number of leaves         :   20 (3555 expanded)
%              Depth                    :   29
%              Number of atoms          :  708 (98132 expanded)
%              Number of equality atoms :  354 (19457 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f52,plain,(
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

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f37,plain,(
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

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

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
   => ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
        | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
        | ~ v1_funct_1(k2_funct_1(sK4)) )
      & k2_relset_1(sK2,sK3,sK4) = sK3
      & v2_funct_1(sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
      | ~ v1_funct_1(k2_funct_1(sK4)) )
    & k2_relset_1(sK2,sK3,sK4) = sK3
    & v2_funct_1(sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f53])).

fof(f92,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f93,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f95,plain,(
    k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

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
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f105,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f86,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f100,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f74,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f72,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
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

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f54])).

fof(f71,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f66])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f103,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f104,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_766,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_40])).

cnf(c_767,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_766])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_769,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_767,c_39])).

cnf(c_1794,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1798,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3578,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1794,c_1798])).

cnf(c_3736,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_769,c_3578])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1797,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3171,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1794,c_1797])).

cnf(c_37,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3183,plain,
    ( k2_relat_1(sK4) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3171,c_37])).

cnf(c_19,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_38,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_478,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_38])).

cnf(c_479,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_481,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_41])).

cnf(c_1792,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2167,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2180,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1792,c_41,c_39,c_479,c_2167])).

cnf(c_3233,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
    inference(demodulation,[status(thm)],[c_3183,c_2180])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_31,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | X2 != X0
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_relat_1(X2) != k1_xboole_0
    | k2_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_31])).

cnf(c_619,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_633,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_619,c_20])).

cnf(c_1786,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1985,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1786,c_10])).

cnf(c_6240,plain,
    ( k1_relset_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK4)),k2_funct_1(sK4)) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3233,c_1985])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_492,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_38])).

cnf(c_493,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_495,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_41])).

cnf(c_1791,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_2176,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1791,c_41,c_39,c_493,c_2167])).

cnf(c_6252,plain,
    ( k1_relset_1(k1_xboole_0,k1_relat_1(sK4),k2_funct_1(sK4)) = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6240,c_2176])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_122,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2168,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2167])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2315,plain,
    ( ~ v1_relat_1(sK4)
    | v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2316,plain,
    ( v1_relat_1(sK4) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2315])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3363,plain,
    ( r1_tarski(k2_funct_1(sK4),k1_xboole_0)
    | r2_hidden(sK1(k2_funct_1(sK4),k1_xboole_0),k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3370,plain,
    ( r1_tarski(k2_funct_1(sK4),k1_xboole_0) = iProver_top
    | r2_hidden(sK1(k2_funct_1(sK4),k1_xboole_0),k2_funct_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3363])).

cnf(c_36,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_777,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(X0) != sK3
    | k2_relat_1(X0) != sK2
    | k2_funct_1(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_36])).

cnf(c_778,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_790,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_778,c_20])).

cnf(c_1779,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_779,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2318,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2319,plain,
    ( v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2318])).

cnf(c_2355,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1779,c_42,c_44,c_779,c_2168,c_2316,c_2319])).

cnf(c_2356,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2355])).

cnf(c_2359,plain,
    ( k1_relat_1(sK4) != sK2
    | k2_relat_1(sK4) != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2356,c_2176,c_2180])).

cnf(c_3231,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3183,c_2359])).

cnf(c_3243,plain,
    ( k1_relat_1(sK4) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3231])).

cnf(c_3893,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3736,c_3243])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_5679,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(X0))
    | ~ r1_tarski(k2_funct_1(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5680,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(k2_funct_1(sK4),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5679])).

cnf(c_5682,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_funct_1(sK4),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5680])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_6820,plain,
    ( ~ r2_hidden(sK1(k2_funct_1(sK4),k1_xboole_0),k2_funct_1(sK4))
    | ~ v1_xboole_0(k2_funct_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6821,plain,
    ( r2_hidden(sK1(k2_funct_1(sK4),k1_xboole_0),k2_funct_1(sK4)) != iProver_top
    | v1_xboole_0(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6820])).

cnf(c_910,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_7249,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_910])).

cnf(c_7250,plain,
    ( sK3 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7249])).

cnf(c_7252,plain,
    ( sK3 != k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7250])).

cnf(c_30,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1796,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4974,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2176,c_1796])).

cnf(c_5000,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4974,c_3233])).

cnf(c_7831,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5000,c_42,c_44,c_2168,c_2316,c_2319])).

cnf(c_7836,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3736,c_7831])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1799,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7839,plain,
    ( v1_xboole_0(k2_funct_1(sK4)) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7831,c_1799])).

cnf(c_8034,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | k1_relset_1(k1_xboole_0,k1_relat_1(sK4),k2_funct_1(sK4)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6252,c_42,c_44,c_122,c_2168,c_2316,c_3370,c_3893,c_5682,c_6821,c_7252,c_7836,c_7839])).

cnf(c_8035,plain,
    ( k1_relset_1(k1_xboole_0,k1_relat_1(sK4),k2_funct_1(sK4)) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8034])).

cnf(c_8038,plain,
    ( k1_relset_1(k1_xboole_0,k1_relat_1(sK4),k2_funct_1(sK4)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8035,c_42,c_44,c_122,c_2168,c_2316,c_3370,c_3893,c_5682,c_6252,c_6821,c_7252,c_7836,c_7839])).

cnf(c_8041,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3736,c_8038])).

cnf(c_8154,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8041,c_3893,c_7836])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1804,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2736,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_1804])).

cnf(c_8196,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8154,c_2736])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_8244,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8196,c_9])).

cnf(c_1805,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k2_relat_1(X2) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_31])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_547,c_20])).

cnf(c_1789,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_2002,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1789,c_9])).

cnf(c_6264,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | sK3 != k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3183,c_2002])).

cnf(c_2642,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2643,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2642])).

cnf(c_2645,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2643])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2703,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2704,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2703])).

cnf(c_2706,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2704])).

cnf(c_3015,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3016,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3015])).

cnf(c_3018,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3016])).

cnf(c_12,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3526,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3529,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3526])).

cnf(c_6656,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6264,c_2645,c_2706,c_3018,c_3529])).

cnf(c_6657,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6656])).

cnf(c_6662,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_6657])).

cnf(c_8557,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8244,c_6662])).

cnf(c_8157,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8154,c_7831])).

cnf(c_8340,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8157,c_10])).

cnf(c_9628,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8557,c_8340])).

cnf(c_3580,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_1798])).

cnf(c_10129,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_9628,c_3580])).

cnf(c_8194,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8154,c_3233])).

cnf(c_9626,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8557,c_8194])).

cnf(c_10137,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10129,c_9626])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_667,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK4) != X0
    | sK2 != X1
    | sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_36])).

cnf(c_668,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_667])).

cnf(c_1784,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_2052,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1784,c_10])).

cnf(c_2447,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | sK3 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2052,c_42,c_44,c_2168,c_2316])).

cnf(c_2448,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2447])).

cnf(c_8198,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8154,c_2448])).

cnf(c_8235,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8198])).

cnf(c_8239,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8235,c_10])).

cnf(c_8343,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_8340,c_8239])).

cnf(c_10493,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8343,c_8557])).

cnf(c_11370,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10137,c_10493])).

cnf(c_114,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_113,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11370,c_114,c_113])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:18:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.38/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/0.98  
% 3.38/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.38/0.98  
% 3.38/0.98  ------  iProver source info
% 3.38/0.98  
% 3.38/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.38/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.38/0.98  git: non_committed_changes: false
% 3.38/0.98  git: last_make_outside_of_git: false
% 3.38/0.98  
% 3.38/0.98  ------ 
% 3.38/0.98  
% 3.38/0.98  ------ Input Options
% 3.38/0.98  
% 3.38/0.98  --out_options                           all
% 3.38/0.98  --tptp_safe_out                         true
% 3.38/0.98  --problem_path                          ""
% 3.38/0.98  --include_path                          ""
% 3.38/0.98  --clausifier                            res/vclausify_rel
% 3.38/0.98  --clausifier_options                    --mode clausify
% 3.38/0.98  --stdin                                 false
% 3.38/0.98  --stats_out                             all
% 3.38/0.98  
% 3.38/0.98  ------ General Options
% 3.38/0.98  
% 3.38/0.98  --fof                                   false
% 3.38/0.98  --time_out_real                         305.
% 3.38/0.98  --time_out_virtual                      -1.
% 3.38/0.98  --symbol_type_check                     false
% 3.38/0.98  --clausify_out                          false
% 3.38/0.98  --sig_cnt_out                           false
% 3.38/0.98  --trig_cnt_out                          false
% 3.38/0.98  --trig_cnt_out_tolerance                1.
% 3.38/0.98  --trig_cnt_out_sk_spl                   false
% 3.38/0.98  --abstr_cl_out                          false
% 3.38/0.98  
% 3.38/0.98  ------ Global Options
% 3.38/0.98  
% 3.38/0.98  --schedule                              default
% 3.38/0.98  --add_important_lit                     false
% 3.38/0.98  --prop_solver_per_cl                    1000
% 3.38/0.98  --min_unsat_core                        false
% 3.38/0.98  --soft_assumptions                      false
% 3.38/0.98  --soft_lemma_size                       3
% 3.38/0.98  --prop_impl_unit_size                   0
% 3.38/0.98  --prop_impl_unit                        []
% 3.38/0.98  --share_sel_clauses                     true
% 3.38/0.98  --reset_solvers                         false
% 3.38/0.98  --bc_imp_inh                            [conj_cone]
% 3.38/0.98  --conj_cone_tolerance                   3.
% 3.38/0.98  --extra_neg_conj                        none
% 3.38/0.98  --large_theory_mode                     true
% 3.38/0.98  --prolific_symb_bound                   200
% 3.38/0.98  --lt_threshold                          2000
% 3.38/0.98  --clause_weak_htbl                      true
% 3.38/0.98  --gc_record_bc_elim                     false
% 3.38/0.98  
% 3.38/0.98  ------ Preprocessing Options
% 3.38/0.98  
% 3.38/0.98  --preprocessing_flag                    true
% 3.38/0.98  --time_out_prep_mult                    0.1
% 3.38/0.98  --splitting_mode                        input
% 3.38/0.98  --splitting_grd                         true
% 3.38/0.98  --splitting_cvd                         false
% 3.38/0.98  --splitting_cvd_svl                     false
% 3.38/0.98  --splitting_nvd                         32
% 3.38/0.98  --sub_typing                            true
% 3.38/0.98  --prep_gs_sim                           true
% 3.38/0.98  --prep_unflatten                        true
% 3.38/0.98  --prep_res_sim                          true
% 3.38/0.98  --prep_upred                            true
% 3.38/0.98  --prep_sem_filter                       exhaustive
% 3.38/0.98  --prep_sem_filter_out                   false
% 3.38/0.98  --pred_elim                             true
% 3.38/0.98  --res_sim_input                         true
% 3.38/0.98  --eq_ax_congr_red                       true
% 3.38/0.98  --pure_diseq_elim                       true
% 3.38/0.98  --brand_transform                       false
% 3.38/0.98  --non_eq_to_eq                          false
% 3.38/0.98  --prep_def_merge                        true
% 3.38/0.98  --prep_def_merge_prop_impl              false
% 3.38/0.98  --prep_def_merge_mbd                    true
% 3.38/0.98  --prep_def_merge_tr_red                 false
% 3.38/0.98  --prep_def_merge_tr_cl                  false
% 3.38/0.98  --smt_preprocessing                     true
% 3.38/0.98  --smt_ac_axioms                         fast
% 3.38/0.98  --preprocessed_out                      false
% 3.38/0.98  --preprocessed_stats                    false
% 3.38/0.98  
% 3.38/0.98  ------ Abstraction refinement Options
% 3.38/0.98  
% 3.38/0.98  --abstr_ref                             []
% 3.38/0.98  --abstr_ref_prep                        false
% 3.38/0.98  --abstr_ref_until_sat                   false
% 3.38/0.98  --abstr_ref_sig_restrict                funpre
% 3.38/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.38/0.98  --abstr_ref_under                       []
% 3.38/0.98  
% 3.38/0.98  ------ SAT Options
% 3.38/0.98  
% 3.38/0.98  --sat_mode                              false
% 3.38/0.98  --sat_fm_restart_options                ""
% 3.38/0.98  --sat_gr_def                            false
% 3.38/0.98  --sat_epr_types                         true
% 3.38/0.98  --sat_non_cyclic_types                  false
% 3.38/0.98  --sat_finite_models                     false
% 3.38/0.98  --sat_fm_lemmas                         false
% 3.38/0.98  --sat_fm_prep                           false
% 3.38/0.98  --sat_fm_uc_incr                        true
% 3.38/0.98  --sat_out_model                         small
% 3.38/0.98  --sat_out_clauses                       false
% 3.38/0.98  
% 3.38/0.98  ------ QBF Options
% 3.38/0.98  
% 3.38/0.98  --qbf_mode                              false
% 3.38/0.98  --qbf_elim_univ                         false
% 3.38/0.98  --qbf_dom_inst                          none
% 3.38/0.98  --qbf_dom_pre_inst                      false
% 3.38/0.98  --qbf_sk_in                             false
% 3.38/0.98  --qbf_pred_elim                         true
% 3.38/0.98  --qbf_split                             512
% 3.38/0.98  
% 3.38/0.98  ------ BMC1 Options
% 3.38/0.98  
% 3.38/0.98  --bmc1_incremental                      false
% 3.38/0.98  --bmc1_axioms                           reachable_all
% 3.38/0.98  --bmc1_min_bound                        0
% 3.38/0.98  --bmc1_max_bound                        -1
% 3.38/0.98  --bmc1_max_bound_default                -1
% 3.38/0.98  --bmc1_symbol_reachability              true
% 3.38/0.98  --bmc1_property_lemmas                  false
% 3.38/0.98  --bmc1_k_induction                      false
% 3.38/0.98  --bmc1_non_equiv_states                 false
% 3.38/0.98  --bmc1_deadlock                         false
% 3.38/0.98  --bmc1_ucm                              false
% 3.38/0.98  --bmc1_add_unsat_core                   none
% 3.38/0.98  --bmc1_unsat_core_children              false
% 3.38/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.38/0.98  --bmc1_out_stat                         full
% 3.38/0.98  --bmc1_ground_init                      false
% 3.38/0.98  --bmc1_pre_inst_next_state              false
% 3.38/0.98  --bmc1_pre_inst_state                   false
% 3.38/0.98  --bmc1_pre_inst_reach_state             false
% 3.38/0.98  --bmc1_out_unsat_core                   false
% 3.38/0.98  --bmc1_aig_witness_out                  false
% 3.38/0.98  --bmc1_verbose                          false
% 3.38/0.98  --bmc1_dump_clauses_tptp                false
% 3.38/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.38/0.98  --bmc1_dump_file                        -
% 3.38/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.38/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.38/0.98  --bmc1_ucm_extend_mode                  1
% 3.38/0.98  --bmc1_ucm_init_mode                    2
% 3.38/0.98  --bmc1_ucm_cone_mode                    none
% 3.38/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.38/0.98  --bmc1_ucm_relax_model                  4
% 3.38/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.38/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.38/0.98  --bmc1_ucm_layered_model                none
% 3.38/0.98  --bmc1_ucm_max_lemma_size               10
% 3.38/0.98  
% 3.38/0.98  ------ AIG Options
% 3.38/0.98  
% 3.38/0.98  --aig_mode                              false
% 3.38/0.98  
% 3.38/0.98  ------ Instantiation Options
% 3.38/0.98  
% 3.38/0.98  --instantiation_flag                    true
% 3.38/0.98  --inst_sos_flag                         false
% 3.38/0.98  --inst_sos_phase                        true
% 3.38/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.38/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.38/0.98  --inst_lit_sel_side                     num_symb
% 3.38/0.98  --inst_solver_per_active                1400
% 3.38/0.98  --inst_solver_calls_frac                1.
% 3.38/0.98  --inst_passive_queue_type               priority_queues
% 3.38/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.38/0.98  --inst_passive_queues_freq              [25;2]
% 3.38/0.98  --inst_dismatching                      true
% 3.38/0.98  --inst_eager_unprocessed_to_passive     true
% 3.38/0.98  --inst_prop_sim_given                   true
% 3.38/0.98  --inst_prop_sim_new                     false
% 3.38/0.98  --inst_subs_new                         false
% 3.38/0.98  --inst_eq_res_simp                      false
% 3.38/0.98  --inst_subs_given                       false
% 3.38/0.98  --inst_orphan_elimination               true
% 3.38/0.98  --inst_learning_loop_flag               true
% 3.38/0.98  --inst_learning_start                   3000
% 3.38/0.98  --inst_learning_factor                  2
% 3.38/0.98  --inst_start_prop_sim_after_learn       3
% 3.38/0.98  --inst_sel_renew                        solver
% 3.38/0.98  --inst_lit_activity_flag                true
% 3.38/0.98  --inst_restr_to_given                   false
% 3.38/0.98  --inst_activity_threshold               500
% 3.38/0.98  --inst_out_proof                        true
% 3.38/0.98  
% 3.38/0.98  ------ Resolution Options
% 3.38/0.98  
% 3.38/0.98  --resolution_flag                       true
% 3.38/0.98  --res_lit_sel                           adaptive
% 3.38/0.98  --res_lit_sel_side                      none
% 3.38/0.98  --res_ordering                          kbo
% 3.38/0.98  --res_to_prop_solver                    active
% 3.38/0.98  --res_prop_simpl_new                    false
% 3.38/0.98  --res_prop_simpl_given                  true
% 3.38/0.98  --res_passive_queue_type                priority_queues
% 3.38/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.38/0.98  --res_passive_queues_freq               [15;5]
% 3.38/0.98  --res_forward_subs                      full
% 3.38/0.98  --res_backward_subs                     full
% 3.38/0.98  --res_forward_subs_resolution           true
% 3.38/0.98  --res_backward_subs_resolution          true
% 3.38/0.98  --res_orphan_elimination                true
% 3.38/0.98  --res_time_limit                        2.
% 3.38/0.98  --res_out_proof                         true
% 3.38/0.98  
% 3.38/0.98  ------ Superposition Options
% 3.38/0.98  
% 3.38/0.98  --superposition_flag                    true
% 3.38/0.98  --sup_passive_queue_type                priority_queues
% 3.38/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.38/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.38/0.98  --demod_completeness_check              fast
% 3.38/0.98  --demod_use_ground                      true
% 3.38/0.98  --sup_to_prop_solver                    passive
% 3.38/0.98  --sup_prop_simpl_new                    true
% 3.38/0.98  --sup_prop_simpl_given                  true
% 3.38/0.98  --sup_fun_splitting                     false
% 3.38/0.98  --sup_smt_interval                      50000
% 3.38/0.98  
% 3.38/0.98  ------ Superposition Simplification Setup
% 3.38/0.98  
% 3.38/0.98  --sup_indices_passive                   []
% 3.38/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.38/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.98  --sup_full_bw                           [BwDemod]
% 3.38/0.98  --sup_immed_triv                        [TrivRules]
% 3.38/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.98  --sup_immed_bw_main                     []
% 3.38/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.38/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/0.98  
% 3.38/0.98  ------ Combination Options
% 3.38/0.98  
% 3.38/0.98  --comb_res_mult                         3
% 3.38/0.98  --comb_sup_mult                         2
% 3.38/0.98  --comb_inst_mult                        10
% 3.38/0.98  
% 3.38/0.98  ------ Debug Options
% 3.38/0.98  
% 3.38/0.98  --dbg_backtrace                         false
% 3.38/0.98  --dbg_dump_prop_clauses                 false
% 3.38/0.98  --dbg_dump_prop_clauses_file            -
% 3.38/0.98  --dbg_out_stat                          false
% 3.38/0.98  ------ Parsing...
% 3.38/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.38/0.98  
% 3.38/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.38/0.98  
% 3.38/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.38/0.98  
% 3.38/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.38/0.98  ------ Proving...
% 3.38/0.98  ------ Problem Properties 
% 3.38/0.98  
% 3.38/0.98  
% 3.38/0.98  clauses                                 43
% 3.38/0.98  conjectures                             3
% 3.38/0.98  EPR                                     6
% 3.38/0.98  Horn                                    34
% 3.38/0.98  unary                                   8
% 3.38/0.98  binary                                  12
% 3.38/0.98  lits                                    121
% 3.38/0.98  lits eq                                 43
% 3.38/0.98  fd_pure                                 0
% 3.38/0.98  fd_pseudo                               0
% 3.38/0.98  fd_cond                                 4
% 3.38/0.98  fd_pseudo_cond                          1
% 3.38/0.98  AC symbols                              0
% 3.38/0.98  
% 3.38/0.98  ------ Schedule dynamic 5 is on 
% 3.38/0.98  
% 3.38/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.38/0.98  
% 3.38/0.98  
% 3.38/0.98  ------ 
% 3.38/0.98  Current options:
% 3.38/0.98  ------ 
% 3.38/0.98  
% 3.38/0.98  ------ Input Options
% 3.38/0.98  
% 3.38/0.98  --out_options                           all
% 3.38/0.98  --tptp_safe_out                         true
% 3.38/0.98  --problem_path                          ""
% 3.38/0.98  --include_path                          ""
% 3.38/0.98  --clausifier                            res/vclausify_rel
% 3.38/0.98  --clausifier_options                    --mode clausify
% 3.38/0.98  --stdin                                 false
% 3.38/0.98  --stats_out                             all
% 3.38/0.98  
% 3.38/0.98  ------ General Options
% 3.38/0.98  
% 3.38/0.98  --fof                                   false
% 3.38/0.98  --time_out_real                         305.
% 3.38/0.98  --time_out_virtual                      -1.
% 3.38/0.98  --symbol_type_check                     false
% 3.38/0.98  --clausify_out                          false
% 3.38/0.98  --sig_cnt_out                           false
% 3.38/0.98  --trig_cnt_out                          false
% 3.38/0.98  --trig_cnt_out_tolerance                1.
% 3.38/0.98  --trig_cnt_out_sk_spl                   false
% 3.38/0.98  --abstr_cl_out                          false
% 3.38/0.98  
% 3.38/0.98  ------ Global Options
% 3.38/0.98  
% 3.38/0.98  --schedule                              default
% 3.38/0.98  --add_important_lit                     false
% 3.38/0.98  --prop_solver_per_cl                    1000
% 3.38/0.98  --min_unsat_core                        false
% 3.38/0.98  --soft_assumptions                      false
% 3.38/0.98  --soft_lemma_size                       3
% 3.38/0.98  --prop_impl_unit_size                   0
% 3.38/0.98  --prop_impl_unit                        []
% 3.38/0.98  --share_sel_clauses                     true
% 3.38/0.98  --reset_solvers                         false
% 3.38/0.98  --bc_imp_inh                            [conj_cone]
% 3.38/0.98  --conj_cone_tolerance                   3.
% 3.38/0.98  --extra_neg_conj                        none
% 3.38/0.98  --large_theory_mode                     true
% 3.38/0.98  --prolific_symb_bound                   200
% 3.38/0.98  --lt_threshold                          2000
% 3.38/0.98  --clause_weak_htbl                      true
% 3.38/0.98  --gc_record_bc_elim                     false
% 3.38/0.98  
% 3.38/0.98  ------ Preprocessing Options
% 3.38/0.98  
% 3.38/0.98  --preprocessing_flag                    true
% 3.38/0.98  --time_out_prep_mult                    0.1
% 3.38/0.98  --splitting_mode                        input
% 3.38/0.98  --splitting_grd                         true
% 3.38/0.98  --splitting_cvd                         false
% 3.38/0.98  --splitting_cvd_svl                     false
% 3.38/0.98  --splitting_nvd                         32
% 3.38/0.98  --sub_typing                            true
% 3.38/0.98  --prep_gs_sim                           true
% 3.38/0.98  --prep_unflatten                        true
% 3.38/0.98  --prep_res_sim                          true
% 3.38/0.98  --prep_upred                            true
% 3.38/0.98  --prep_sem_filter                       exhaustive
% 3.38/0.98  --prep_sem_filter_out                   false
% 3.38/0.98  --pred_elim                             true
% 3.38/0.98  --res_sim_input                         true
% 3.38/0.98  --eq_ax_congr_red                       true
% 3.38/0.98  --pure_diseq_elim                       true
% 3.38/0.98  --brand_transform                       false
% 3.38/0.98  --non_eq_to_eq                          false
% 3.38/0.98  --prep_def_merge                        true
% 3.38/0.98  --prep_def_merge_prop_impl              false
% 3.38/0.98  --prep_def_merge_mbd                    true
% 3.38/0.98  --prep_def_merge_tr_red                 false
% 3.38/0.98  --prep_def_merge_tr_cl                  false
% 3.38/0.98  --smt_preprocessing                     true
% 3.38/0.98  --smt_ac_axioms                         fast
% 3.38/0.98  --preprocessed_out                      false
% 3.38/0.98  --preprocessed_stats                    false
% 3.38/0.98  
% 3.38/0.98  ------ Abstraction refinement Options
% 3.38/0.98  
% 3.38/0.98  --abstr_ref                             []
% 3.38/0.98  --abstr_ref_prep                        false
% 3.38/0.98  --abstr_ref_until_sat                   false
% 3.38/0.98  --abstr_ref_sig_restrict                funpre
% 3.38/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.38/0.98  --abstr_ref_under                       []
% 3.38/0.98  
% 3.38/0.98  ------ SAT Options
% 3.38/0.98  
% 3.38/0.98  --sat_mode                              false
% 3.38/0.98  --sat_fm_restart_options                ""
% 3.38/0.98  --sat_gr_def                            false
% 3.38/0.98  --sat_epr_types                         true
% 3.38/0.98  --sat_non_cyclic_types                  false
% 3.38/0.98  --sat_finite_models                     false
% 3.38/0.98  --sat_fm_lemmas                         false
% 3.38/0.98  --sat_fm_prep                           false
% 3.38/0.98  --sat_fm_uc_incr                        true
% 3.38/0.98  --sat_out_model                         small
% 3.38/0.98  --sat_out_clauses                       false
% 3.38/0.98  
% 3.38/0.98  ------ QBF Options
% 3.38/0.98  
% 3.38/0.98  --qbf_mode                              false
% 3.38/0.98  --qbf_elim_univ                         false
% 3.38/0.98  --qbf_dom_inst                          none
% 3.38/0.98  --qbf_dom_pre_inst                      false
% 3.38/0.98  --qbf_sk_in                             false
% 3.38/0.98  --qbf_pred_elim                         true
% 3.38/0.98  --qbf_split                             512
% 3.38/0.98  
% 3.38/0.98  ------ BMC1 Options
% 3.38/0.98  
% 3.38/0.98  --bmc1_incremental                      false
% 3.38/0.98  --bmc1_axioms                           reachable_all
% 3.38/0.98  --bmc1_min_bound                        0
% 3.38/0.98  --bmc1_max_bound                        -1
% 3.38/0.98  --bmc1_max_bound_default                -1
% 3.38/0.98  --bmc1_symbol_reachability              true
% 3.38/0.99  --bmc1_property_lemmas                  false
% 3.38/0.99  --bmc1_k_induction                      false
% 3.38/0.99  --bmc1_non_equiv_states                 false
% 3.38/0.99  --bmc1_deadlock                         false
% 3.38/0.99  --bmc1_ucm                              false
% 3.38/0.99  --bmc1_add_unsat_core                   none
% 3.38/0.99  --bmc1_unsat_core_children              false
% 3.38/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.38/0.99  --bmc1_out_stat                         full
% 3.38/0.99  --bmc1_ground_init                      false
% 3.38/0.99  --bmc1_pre_inst_next_state              false
% 3.38/0.99  --bmc1_pre_inst_state                   false
% 3.38/0.99  --bmc1_pre_inst_reach_state             false
% 3.38/0.99  --bmc1_out_unsat_core                   false
% 3.38/0.99  --bmc1_aig_witness_out                  false
% 3.38/0.99  --bmc1_verbose                          false
% 3.38/0.99  --bmc1_dump_clauses_tptp                false
% 3.38/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.38/0.99  --bmc1_dump_file                        -
% 3.38/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.38/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.38/0.99  --bmc1_ucm_extend_mode                  1
% 3.38/0.99  --bmc1_ucm_init_mode                    2
% 3.38/0.99  --bmc1_ucm_cone_mode                    none
% 3.38/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.38/0.99  --bmc1_ucm_relax_model                  4
% 3.38/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.38/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.38/0.99  --bmc1_ucm_layered_model                none
% 3.38/0.99  --bmc1_ucm_max_lemma_size               10
% 3.38/0.99  
% 3.38/0.99  ------ AIG Options
% 3.38/0.99  
% 3.38/0.99  --aig_mode                              false
% 3.38/0.99  
% 3.38/0.99  ------ Instantiation Options
% 3.38/0.99  
% 3.38/0.99  --instantiation_flag                    true
% 3.38/0.99  --inst_sos_flag                         false
% 3.38/0.99  --inst_sos_phase                        true
% 3.38/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.38/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.38/0.99  --inst_lit_sel_side                     none
% 3.38/0.99  --inst_solver_per_active                1400
% 3.38/0.99  --inst_solver_calls_frac                1.
% 3.38/0.99  --inst_passive_queue_type               priority_queues
% 3.38/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.38/0.99  --inst_passive_queues_freq              [25;2]
% 3.38/0.99  --inst_dismatching                      true
% 3.38/0.99  --inst_eager_unprocessed_to_passive     true
% 3.38/0.99  --inst_prop_sim_given                   true
% 3.38/0.99  --inst_prop_sim_new                     false
% 3.38/0.99  --inst_subs_new                         false
% 3.38/0.99  --inst_eq_res_simp                      false
% 3.38/0.99  --inst_subs_given                       false
% 3.38/0.99  --inst_orphan_elimination               true
% 3.38/0.99  --inst_learning_loop_flag               true
% 3.38/0.99  --inst_learning_start                   3000
% 3.38/0.99  --inst_learning_factor                  2
% 3.38/0.99  --inst_start_prop_sim_after_learn       3
% 3.38/0.99  --inst_sel_renew                        solver
% 3.38/0.99  --inst_lit_activity_flag                true
% 3.38/0.99  --inst_restr_to_given                   false
% 3.38/0.99  --inst_activity_threshold               500
% 3.38/0.99  --inst_out_proof                        true
% 3.38/0.99  
% 3.38/0.99  ------ Resolution Options
% 3.38/0.99  
% 3.38/0.99  --resolution_flag                       false
% 3.38/0.99  --res_lit_sel                           adaptive
% 3.38/0.99  --res_lit_sel_side                      none
% 3.38/0.99  --res_ordering                          kbo
% 3.38/0.99  --res_to_prop_solver                    active
% 3.38/0.99  --res_prop_simpl_new                    false
% 3.38/0.99  --res_prop_simpl_given                  true
% 3.38/0.99  --res_passive_queue_type                priority_queues
% 3.38/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.38/0.99  --res_passive_queues_freq               [15;5]
% 3.38/0.99  --res_forward_subs                      full
% 3.38/0.99  --res_backward_subs                     full
% 3.38/0.99  --res_forward_subs_resolution           true
% 3.38/0.99  --res_backward_subs_resolution          true
% 3.38/0.99  --res_orphan_elimination                true
% 3.38/0.99  --res_time_limit                        2.
% 3.38/0.99  --res_out_proof                         true
% 3.38/0.99  
% 3.38/0.99  ------ Superposition Options
% 3.38/0.99  
% 3.38/0.99  --superposition_flag                    true
% 3.38/0.99  --sup_passive_queue_type                priority_queues
% 3.38/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.38/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.38/0.99  --demod_completeness_check              fast
% 3.38/0.99  --demod_use_ground                      true
% 3.38/0.99  --sup_to_prop_solver                    passive
% 3.38/0.99  --sup_prop_simpl_new                    true
% 3.38/0.99  --sup_prop_simpl_given                  true
% 3.38/0.99  --sup_fun_splitting                     false
% 3.38/0.99  --sup_smt_interval                      50000
% 3.38/0.99  
% 3.38/0.99  ------ Superposition Simplification Setup
% 3.38/0.99  
% 3.38/0.99  --sup_indices_passive                   []
% 3.38/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.38/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.99  --sup_full_bw                           [BwDemod]
% 3.38/0.99  --sup_immed_triv                        [TrivRules]
% 3.38/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.99  --sup_immed_bw_main                     []
% 3.38/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.38/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/0.99  
% 3.38/0.99  ------ Combination Options
% 3.38/0.99  
% 3.38/0.99  --comb_res_mult                         3
% 3.38/0.99  --comb_sup_mult                         2
% 3.38/0.99  --comb_inst_mult                        10
% 3.38/0.99  
% 3.38/0.99  ------ Debug Options
% 3.38/0.99  
% 3.38/0.99  --dbg_backtrace                         false
% 3.38/0.99  --dbg_dump_prop_clauses                 false
% 3.38/0.99  --dbg_dump_prop_clauses_file            -
% 3.38/0.99  --dbg_out_stat                          false
% 3.38/0.99  
% 3.38/0.99  
% 3.38/0.99  
% 3.38/0.99  
% 3.38/0.99  ------ Proving...
% 3.38/0.99  
% 3.38/0.99  
% 3.38/0.99  % SZS status Theorem for theBenchmark.p
% 3.38/0.99  
% 3.38/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.38/0.99  
% 3.38/0.99  fof(f15,axiom,(
% 3.38/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f31,plain,(
% 3.38/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.99    inference(ennf_transformation,[],[f15])).
% 3.38/0.99  
% 3.38/0.99  fof(f32,plain,(
% 3.38/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.99    inference(flattening,[],[f31])).
% 3.38/0.99  
% 3.38/0.99  fof(f52,plain,(
% 3.38/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.99    inference(nnf_transformation,[],[f32])).
% 3.38/0.99  
% 3.38/0.99  fof(f79,plain,(
% 3.38/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/0.99    inference(cnf_transformation,[],[f52])).
% 3.38/0.99  
% 3.38/0.99  fof(f18,conjecture,(
% 3.38/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f19,negated_conjecture,(
% 3.38/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.38/0.99    inference(negated_conjecture,[],[f18])).
% 3.38/0.99  
% 3.38/0.99  fof(f37,plain,(
% 3.38/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.38/0.99    inference(ennf_transformation,[],[f19])).
% 3.38/0.99  
% 3.38/0.99  fof(f38,plain,(
% 3.38/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.38/0.99    inference(flattening,[],[f37])).
% 3.38/0.99  
% 3.38/0.99  fof(f53,plain,(
% 3.38/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 3.38/0.99    introduced(choice_axiom,[])).
% 3.38/0.99  
% 3.38/0.99  fof(f54,plain,(
% 3.38/0.99    (~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 3.38/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f53])).
% 3.38/0.99  
% 3.38/0.99  fof(f92,plain,(
% 3.38/0.99    v1_funct_2(sK4,sK2,sK3)),
% 3.38/0.99    inference(cnf_transformation,[],[f54])).
% 3.38/0.99  
% 3.38/0.99  fof(f93,plain,(
% 3.38/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.38/0.99    inference(cnf_transformation,[],[f54])).
% 3.38/0.99  
% 3.38/0.99  fof(f13,axiom,(
% 3.38/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f29,plain,(
% 3.38/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.99    inference(ennf_transformation,[],[f13])).
% 3.38/0.99  
% 3.38/0.99  fof(f77,plain,(
% 3.38/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/0.99    inference(cnf_transformation,[],[f29])).
% 3.38/0.99  
% 3.38/0.99  fof(f14,axiom,(
% 3.38/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f30,plain,(
% 3.38/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.99    inference(ennf_transformation,[],[f14])).
% 3.38/0.99  
% 3.38/0.99  fof(f78,plain,(
% 3.38/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/0.99    inference(cnf_transformation,[],[f30])).
% 3.38/0.99  
% 3.38/0.99  fof(f95,plain,(
% 3.38/0.99    k2_relset_1(sK2,sK3,sK4) = sK3),
% 3.38/0.99    inference(cnf_transformation,[],[f54])).
% 3.38/0.99  
% 3.38/0.99  fof(f10,axiom,(
% 3.38/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f25,plain,(
% 3.38/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.38/0.99    inference(ennf_transformation,[],[f10])).
% 3.38/0.99  
% 3.38/0.99  fof(f26,plain,(
% 3.38/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.38/0.99    inference(flattening,[],[f25])).
% 3.38/0.99  
% 3.38/0.99  fof(f73,plain,(
% 3.38/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f26])).
% 3.38/0.99  
% 3.38/0.99  fof(f94,plain,(
% 3.38/0.99    v2_funct_1(sK4)),
% 3.38/0.99    inference(cnf_transformation,[],[f54])).
% 3.38/0.99  
% 3.38/0.99  fof(f91,plain,(
% 3.38/0.99    v1_funct_1(sK4)),
% 3.38/0.99    inference(cnf_transformation,[],[f54])).
% 3.38/0.99  
% 3.38/0.99  fof(f11,axiom,(
% 3.38/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f27,plain,(
% 3.38/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.38/0.99    inference(ennf_transformation,[],[f11])).
% 3.38/0.99  
% 3.38/0.99  fof(f75,plain,(
% 3.38/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/0.99    inference(cnf_transformation,[],[f27])).
% 3.38/0.99  
% 3.38/0.99  fof(f80,plain,(
% 3.38/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/0.99    inference(cnf_transformation,[],[f52])).
% 3.38/0.99  
% 3.38/0.99  fof(f105,plain,(
% 3.38/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.38/0.99    inference(equality_resolution,[],[f80])).
% 3.38/0.99  
% 3.38/0.99  fof(f16,axiom,(
% 3.38/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f33,plain,(
% 3.38/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.38/0.99    inference(ennf_transformation,[],[f16])).
% 3.38/0.99  
% 3.38/0.99  fof(f34,plain,(
% 3.38/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.38/0.99    inference(flattening,[],[f33])).
% 3.38/0.99  
% 3.38/0.99  fof(f86,plain,(
% 3.38/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f34])).
% 3.38/0.99  
% 3.38/0.99  fof(f5,axiom,(
% 3.38/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f49,plain,(
% 3.38/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.38/0.99    inference(nnf_transformation,[],[f5])).
% 3.38/0.99  
% 3.38/0.99  fof(f50,plain,(
% 3.38/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.38/0.99    inference(flattening,[],[f49])).
% 3.38/0.99  
% 3.38/0.99  fof(f65,plain,(
% 3.38/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.38/0.99    inference(cnf_transformation,[],[f50])).
% 3.38/0.99  
% 3.38/0.99  fof(f100,plain,(
% 3.38/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.38/0.99    inference(equality_resolution,[],[f65])).
% 3.38/0.99  
% 3.38/0.99  fof(f74,plain,(
% 3.38/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f26])).
% 3.38/0.99  
% 3.38/0.99  fof(f3,axiom,(
% 3.38/0.99    v1_xboole_0(k1_xboole_0)),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f60,plain,(
% 3.38/0.99    v1_xboole_0(k1_xboole_0)),
% 3.38/0.99    inference(cnf_transformation,[],[f3])).
% 3.38/0.99  
% 3.38/0.99  fof(f9,axiom,(
% 3.38/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f23,plain,(
% 3.38/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.38/0.99    inference(ennf_transformation,[],[f9])).
% 3.38/0.99  
% 3.38/0.99  fof(f24,plain,(
% 3.38/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.38/0.99    inference(flattening,[],[f23])).
% 3.38/0.99  
% 3.38/0.99  fof(f72,plain,(
% 3.38/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f24])).
% 3.38/0.99  
% 3.38/0.99  fof(f2,axiom,(
% 3.38/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f20,plain,(
% 3.38/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.38/0.99    inference(ennf_transformation,[],[f2])).
% 3.38/0.99  
% 3.38/0.99  fof(f43,plain,(
% 3.38/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.38/0.99    inference(nnf_transformation,[],[f20])).
% 3.38/0.99  
% 3.38/0.99  fof(f44,plain,(
% 3.38/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.38/0.99    inference(rectify,[],[f43])).
% 3.38/0.99  
% 3.38/0.99  fof(f45,plain,(
% 3.38/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.38/0.99    introduced(choice_axiom,[])).
% 3.38/0.99  
% 3.38/0.99  fof(f46,plain,(
% 3.38/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.38/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).
% 3.38/0.99  
% 3.38/0.99  fof(f58,plain,(
% 3.38/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f46])).
% 3.38/0.99  
% 3.38/0.99  fof(f96,plain,(
% 3.38/0.99    ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))),
% 3.38/0.99    inference(cnf_transformation,[],[f54])).
% 3.38/0.99  
% 3.38/0.99  fof(f71,plain,(
% 3.38/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f24])).
% 3.38/0.99  
% 3.38/0.99  fof(f7,axiom,(
% 3.38/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f51,plain,(
% 3.38/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.38/0.99    inference(nnf_transformation,[],[f7])).
% 3.38/0.99  
% 3.38/0.99  fof(f69,plain,(
% 3.38/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f51])).
% 3.38/0.99  
% 3.38/0.99  fof(f1,axiom,(
% 3.38/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f39,plain,(
% 3.38/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.38/0.99    inference(nnf_transformation,[],[f1])).
% 3.38/0.99  
% 3.38/0.99  fof(f40,plain,(
% 3.38/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.38/0.99    inference(rectify,[],[f39])).
% 3.38/0.99  
% 3.38/0.99  fof(f41,plain,(
% 3.38/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.38/0.99    introduced(choice_axiom,[])).
% 3.38/0.99  
% 3.38/0.99  fof(f42,plain,(
% 3.38/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.38/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.38/0.99  
% 3.38/0.99  fof(f55,plain,(
% 3.38/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f42])).
% 3.38/0.99  
% 3.38/0.99  fof(f87,plain,(
% 3.38/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f34])).
% 3.38/0.99  
% 3.38/0.99  fof(f12,axiom,(
% 3.38/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f28,plain,(
% 3.38/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.38/0.99    inference(ennf_transformation,[],[f12])).
% 3.38/0.99  
% 3.38/0.99  fof(f76,plain,(
% 3.38/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f28])).
% 3.38/0.99  
% 3.38/0.99  fof(f68,plain,(
% 3.38/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.38/0.99    inference(cnf_transformation,[],[f51])).
% 3.38/0.99  
% 3.38/0.99  fof(f66,plain,(
% 3.38/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.38/0.99    inference(cnf_transformation,[],[f50])).
% 3.38/0.99  
% 3.38/0.99  fof(f99,plain,(
% 3.38/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.38/0.99    inference(equality_resolution,[],[f66])).
% 3.38/0.99  
% 3.38/0.99  fof(f83,plain,(
% 3.38/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/0.99    inference(cnf_transformation,[],[f52])).
% 3.38/0.99  
% 3.38/0.99  fof(f103,plain,(
% 3.38/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.38/0.99    inference(equality_resolution,[],[f83])).
% 3.38/0.99  
% 3.38/0.99  fof(f4,axiom,(
% 3.38/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f47,plain,(
% 3.38/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.38/0.99    inference(nnf_transformation,[],[f4])).
% 3.38/0.99  
% 3.38/0.99  fof(f48,plain,(
% 3.38/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.38/0.99    inference(flattening,[],[f47])).
% 3.38/0.99  
% 3.38/0.99  fof(f63,plain,(
% 3.38/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f48])).
% 3.38/0.99  
% 3.38/0.99  fof(f6,axiom,(
% 3.38/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.38/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.38/0.99  
% 3.38/0.99  fof(f67,plain,(
% 3.38/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.38/0.99    inference(cnf_transformation,[],[f6])).
% 3.38/0.99  
% 3.38/0.99  fof(f82,plain,(
% 3.38/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.38/0.99    inference(cnf_transformation,[],[f52])).
% 3.38/0.99  
% 3.38/0.99  fof(f104,plain,(
% 3.38/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.38/0.99    inference(equality_resolution,[],[f82])).
% 3.38/0.99  
% 3.38/0.99  fof(f64,plain,(
% 3.38/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.38/0.99    inference(cnf_transformation,[],[f50])).
% 3.38/0.99  
% 3.38/0.99  cnf(c_29,plain,
% 3.38/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.38/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.38/0.99      | k1_xboole_0 = X2 ),
% 3.38/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_40,negated_conjecture,
% 3.38/0.99      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.38/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_766,plain,
% 3.38/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.38/0.99      | sK2 != X1
% 3.38/0.99      | sK3 != X2
% 3.38/0.99      | sK4 != X0
% 3.38/0.99      | k1_xboole_0 = X2 ),
% 3.38/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_40]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_767,plain,
% 3.38/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.38/0.99      | k1_relset_1(sK2,sK3,sK4) = sK2
% 3.38/0.99      | k1_xboole_0 = sK3 ),
% 3.38/0.99      inference(unflattening,[status(thm)],[c_766]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_39,negated_conjecture,
% 3.38/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.38/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_769,plain,
% 3.38/0.99      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 3.38/0.99      inference(global_propositional_subsumption,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_767,c_39]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1794,plain,
% 3.38/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_22,plain,
% 3.38/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.38/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1798,plain,
% 3.38/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.38/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3578,plain,
% 3.38/0.99      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_1794,c_1798]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3736,plain,
% 3.38/0.99      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_769,c_3578]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_23,plain,
% 3.38/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.38/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1797,plain,
% 3.38/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.38/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3171,plain,
% 3.38/0.99      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_1794,c_1797]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_37,negated_conjecture,
% 3.38/0.99      ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
% 3.38/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3183,plain,
% 3.38/0.99      ( k2_relat_1(sK4) = sK3 ),
% 3.38/0.99      inference(light_normalisation,[status(thm)],[c_3171,c_37]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_19,plain,
% 3.38/0.99      ( ~ v2_funct_1(X0)
% 3.38/0.99      | ~ v1_relat_1(X0)
% 3.38/0.99      | ~ v1_funct_1(X0)
% 3.38/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.38/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_38,negated_conjecture,
% 3.38/0.99      ( v2_funct_1(sK4) ),
% 3.38/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_478,plain,
% 3.38/0.99      ( ~ v1_relat_1(X0)
% 3.38/0.99      | ~ v1_funct_1(X0)
% 3.38/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.38/0.99      | sK4 != X0 ),
% 3.38/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_38]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_479,plain,
% 3.38/0.99      ( ~ v1_relat_1(sK4)
% 3.38/0.99      | ~ v1_funct_1(sK4)
% 3.38/0.99      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.38/0.99      inference(unflattening,[status(thm)],[c_478]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_41,negated_conjecture,
% 3.38/0.99      ( v1_funct_1(sK4) ),
% 3.38/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_481,plain,
% 3.38/0.99      ( ~ v1_relat_1(sK4)
% 3.38/0.99      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.38/0.99      inference(global_propositional_subsumption,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_479,c_41]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1792,plain,
% 3.38/0.99      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 3.38/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_20,plain,
% 3.38/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/0.99      | v1_relat_1(X0) ),
% 3.38/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2167,plain,
% 3.38/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.38/0.99      | v1_relat_1(sK4) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2180,plain,
% 3.38/0.99      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.38/0.99      inference(global_propositional_subsumption,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_1792,c_41,c_39,c_479,c_2167]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3233,plain,
% 3.38/0.99      ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
% 3.38/0.99      inference(demodulation,[status(thm)],[c_3183,c_2180]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_28,plain,
% 3.38/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.38/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.38/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.38/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_31,plain,
% 3.38/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.38/0.99      | ~ v1_relat_1(X0)
% 3.38/0.99      | ~ v1_funct_1(X0) ),
% 3.38/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_618,plain,
% 3.38/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.38/0.99      | ~ v1_relat_1(X2)
% 3.38/0.99      | ~ v1_funct_1(X2)
% 3.38/0.99      | X2 != X0
% 3.38/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.38/0.99      | k1_relat_1(X2) != k1_xboole_0
% 3.38/0.99      | k2_relat_1(X2) != X1 ),
% 3.38/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_31]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_619,plain,
% 3.38/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
% 3.38/0.99      | ~ v1_relat_1(X0)
% 3.38/0.99      | ~ v1_funct_1(X0)
% 3.38/0.99      | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 3.38/0.99      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.38/0.99      inference(unflattening,[status(thm)],[c_618]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_633,plain,
% 3.38/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0))))
% 3.38/0.99      | ~ v1_funct_1(X0)
% 3.38/0.99      | k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 3.38/0.99      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.38/0.99      inference(forward_subsumption_resolution,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_619,c_20]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1786,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 3.38/0.99      | k1_relat_1(X0) != k1_xboole_0
% 3.38/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(X0)))) != iProver_top
% 3.38/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_10,plain,
% 3.38/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.38/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1985,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,k2_relat_1(X0),X0) = k1_xboole_0
% 3.38/0.99      | k1_relat_1(X0) != k1_xboole_0
% 3.38/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.38/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.38/0.99      inference(demodulation,[status(thm)],[c_1786,c_10]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_6240,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK4)),k2_funct_1(sK4)) = k1_xboole_0
% 3.38/0.99      | sK3 != k1_xboole_0
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.38/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_3233,c_1985]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_18,plain,
% 3.38/0.99      ( ~ v2_funct_1(X0)
% 3.38/0.99      | ~ v1_relat_1(X0)
% 3.38/0.99      | ~ v1_funct_1(X0)
% 3.38/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.38/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_492,plain,
% 3.38/0.99      ( ~ v1_relat_1(X0)
% 3.38/0.99      | ~ v1_funct_1(X0)
% 3.38/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.38/0.99      | sK4 != X0 ),
% 3.38/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_38]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_493,plain,
% 3.38/0.99      ( ~ v1_relat_1(sK4)
% 3.38/0.99      | ~ v1_funct_1(sK4)
% 3.38/0.99      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.38/0.99      inference(unflattening,[status(thm)],[c_492]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_495,plain,
% 3.38/0.99      ( ~ v1_relat_1(sK4)
% 3.38/0.99      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.38/0.99      inference(global_propositional_subsumption,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_493,c_41]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1791,plain,
% 3.38/0.99      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 3.38/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2176,plain,
% 3.38/0.99      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.38/0.99      inference(global_propositional_subsumption,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_1791,c_41,c_39,c_493,c_2167]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_6252,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,k1_relat_1(sK4),k2_funct_1(sK4)) = k1_xboole_0
% 3.38/0.99      | sK3 != k1_xboole_0
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.38/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.38/0.99      inference(light_normalisation,[status(thm)],[c_6240,c_2176]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_42,plain,
% 3.38/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_44,plain,
% 3.38/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_5,plain,
% 3.38/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.38/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_122,plain,
% 3.38/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2168,plain,
% 3.38/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.38/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_2167]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_16,plain,
% 3.38/0.99      ( ~ v1_relat_1(X0)
% 3.38/0.99      | ~ v1_funct_1(X0)
% 3.38/0.99      | v1_funct_1(k2_funct_1(X0)) ),
% 3.38/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2315,plain,
% 3.38/0.99      ( ~ v1_relat_1(sK4)
% 3.38/0.99      | v1_funct_1(k2_funct_1(sK4))
% 3.38/0.99      | ~ v1_funct_1(sK4) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2316,plain,
% 3.38/0.99      ( v1_relat_1(sK4) != iProver_top
% 3.38/0.99      | v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 3.38/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_2315]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3,plain,
% 3.38/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.38/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3363,plain,
% 3.38/0.99      ( r1_tarski(k2_funct_1(sK4),k1_xboole_0)
% 3.38/0.99      | r2_hidden(sK1(k2_funct_1(sK4),k1_xboole_0),k2_funct_1(sK4)) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3370,plain,
% 3.38/0.99      ( r1_tarski(k2_funct_1(sK4),k1_xboole_0) = iProver_top
% 3.38/0.99      | r2_hidden(sK1(k2_funct_1(sK4),k1_xboole_0),k2_funct_1(sK4)) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_3363]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_36,negated_conjecture,
% 3.38/0.99      ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
% 3.38/0.99      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.38/0.99      | ~ v1_funct_1(k2_funct_1(sK4)) ),
% 3.38/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_777,plain,
% 3.38/0.99      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.38/0.99      | ~ v1_relat_1(X0)
% 3.38/0.99      | ~ v1_funct_1(X0)
% 3.38/0.99      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.38/0.99      | k1_relat_1(X0) != sK3
% 3.38/0.99      | k2_relat_1(X0) != sK2
% 3.38/0.99      | k2_funct_1(sK4) != X0 ),
% 3.38/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_36]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_778,plain,
% 3.38/0.99      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.38/0.99      | ~ v1_relat_1(k2_funct_1(sK4))
% 3.38/0.99      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.38/0.99      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.38/0.99      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 3.38/0.99      inference(unflattening,[status(thm)],[c_777]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_790,plain,
% 3.38/0.99      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.38/0.99      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.38/0.99      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.38/0.99      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 3.38/0.99      inference(forward_subsumption_resolution,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_778,c_20]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1779,plain,
% 3.38/0.99      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.38/0.99      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.38/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_779,plain,
% 3.38/0.99      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.38/0.99      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.38/0.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 3.38/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_17,plain,
% 3.38/0.99      ( ~ v1_relat_1(X0)
% 3.38/0.99      | v1_relat_1(k2_funct_1(X0))
% 3.38/0.99      | ~ v1_funct_1(X0) ),
% 3.38/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2318,plain,
% 3.38/0.99      ( v1_relat_1(k2_funct_1(sK4))
% 3.38/0.99      | ~ v1_relat_1(sK4)
% 3.38/0.99      | ~ v1_funct_1(sK4) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2319,plain,
% 3.38/0.99      ( v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 3.38/0.99      | v1_relat_1(sK4) != iProver_top
% 3.38/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_2318]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2355,plain,
% 3.38/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.38/0.99      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.38/0.99      | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
% 3.38/0.99      inference(global_propositional_subsumption,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_1779,c_42,c_44,c_779,c_2168,c_2316,c_2319]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2356,plain,
% 3.38/0.99      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.38/0.99      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.38/0.99      inference(renaming,[status(thm)],[c_2355]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2359,plain,
% 3.38/0.99      ( k1_relat_1(sK4) != sK2
% 3.38/0.99      | k2_relat_1(sK4) != sK3
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.38/0.99      inference(light_normalisation,[status(thm)],[c_2356,c_2176,c_2180]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3231,plain,
% 3.38/0.99      ( k1_relat_1(sK4) != sK2
% 3.38/0.99      | sK3 != sK3
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.38/0.99      inference(demodulation,[status(thm)],[c_3183,c_2359]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3243,plain,
% 3.38/0.99      ( k1_relat_1(sK4) != sK2
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.38/0.99      inference(equality_resolution_simp,[status(thm)],[c_3231]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3893,plain,
% 3.38/0.99      ( sK3 = k1_xboole_0
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_3736,c_3243]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_13,plain,
% 3.38/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.38/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_5679,plain,
% 3.38/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(X0))
% 3.38/0.99      | ~ r1_tarski(k2_funct_1(sK4),X0) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_5680,plain,
% 3.38/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(X0)) = iProver_top
% 3.38/0.99      | r1_tarski(k2_funct_1(sK4),X0) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_5679]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_5682,plain,
% 3.38/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.38/0.99      | r1_tarski(k2_funct_1(sK4),k1_xboole_0) != iProver_top ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_5680]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1,plain,
% 3.38/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.38/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_6820,plain,
% 3.38/0.99      ( ~ r2_hidden(sK1(k2_funct_1(sK4),k1_xboole_0),k2_funct_1(sK4))
% 3.38/0.99      | ~ v1_xboole_0(k2_funct_1(sK4)) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_6821,plain,
% 3.38/0.99      ( r2_hidden(sK1(k2_funct_1(sK4),k1_xboole_0),k2_funct_1(sK4)) != iProver_top
% 3.38/0.99      | v1_xboole_0(k2_funct_1(sK4)) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_6820]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_910,plain,
% 3.38/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.38/0.99      theory(equality) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_7249,plain,
% 3.38/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_910]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_7250,plain,
% 3.38/0.99      ( sK3 != X0
% 3.38/0.99      | v1_xboole_0(X0) != iProver_top
% 3.38/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_7249]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_7252,plain,
% 3.38/0.99      ( sK3 != k1_xboole_0
% 3.38/0.99      | v1_xboole_0(sK3) = iProver_top
% 3.38/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_7250]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_30,plain,
% 3.38/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.38/0.99      | ~ v1_relat_1(X0)
% 3.38/0.99      | ~ v1_funct_1(X0) ),
% 3.38/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1796,plain,
% 3.38/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.38/0.99      | v1_relat_1(X0) != iProver_top
% 3.38/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_4974,plain,
% 3.38/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK4)),k1_relat_1(sK4)))) = iProver_top
% 3.38/0.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 3.38/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_2176,c_1796]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_5000,plain,
% 3.38/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
% 3.38/0.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 3.38/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.38/0.99      inference(light_normalisation,[status(thm)],[c_4974,c_3233]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_7831,plain,
% 3.38/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
% 3.38/0.99      inference(global_propositional_subsumption,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_5000,c_42,c_44,c_2168,c_2316,c_2319]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_7836,plain,
% 3.38/0.99      ( sK3 = k1_xboole_0
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_3736,c_7831]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_21,plain,
% 3.38/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.38/0.99      | ~ v1_xboole_0(X1)
% 3.38/0.99      | v1_xboole_0(X0) ),
% 3.38/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1799,plain,
% 3.38/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.38/0.99      | v1_xboole_0(X1) != iProver_top
% 3.38/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_7839,plain,
% 3.38/0.99      ( v1_xboole_0(k2_funct_1(sK4)) = iProver_top
% 3.38/0.99      | v1_xboole_0(sK3) != iProver_top ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_7831,c_1799]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_8034,plain,
% 3.38/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.38/0.99      | k1_relset_1(k1_xboole_0,k1_relat_1(sK4),k2_funct_1(sK4)) = k1_xboole_0 ),
% 3.38/0.99      inference(global_propositional_subsumption,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_6252,c_42,c_44,c_122,c_2168,c_2316,c_3370,c_3893,
% 3.38/0.99                 c_5682,c_6821,c_7252,c_7836,c_7839]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_8035,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,k1_relat_1(sK4),k2_funct_1(sK4)) = k1_xboole_0
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.38/0.99      inference(renaming,[status(thm)],[c_8034]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_8038,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,k1_relat_1(sK4),k2_funct_1(sK4)) = k1_xboole_0 ),
% 3.38/0.99      inference(global_propositional_subsumption,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_8035,c_42,c_44,c_122,c_2168,c_2316,c_3370,c_3893,
% 3.38/0.99                 c_5682,c_6252,c_6821,c_7252,c_7836,c_7839]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_8041,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) = k1_xboole_0
% 3.38/0.99      | sK3 = k1_xboole_0 ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_3736,c_8038]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_8154,plain,
% 3.38/0.99      ( sK3 = k1_xboole_0 ),
% 3.38/0.99      inference(global_propositional_subsumption,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_8041,c_3893,c_7836]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_14,plain,
% 3.38/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.38/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1804,plain,
% 3.38/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.38/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2736,plain,
% 3.38/0.99      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_1794,c_1804]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_8196,plain,
% 3.38/0.99      ( r1_tarski(sK4,k2_zfmisc_1(sK2,k1_xboole_0)) = iProver_top ),
% 3.38/0.99      inference(demodulation,[status(thm)],[c_8154,c_2736]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_9,plain,
% 3.38/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.38/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_8244,plain,
% 3.38/0.99      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.38/0.99      inference(demodulation,[status(thm)],[c_8196,c_9]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1805,plain,
% 3.38/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.38/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_25,plain,
% 3.38/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.38/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.38/0.99      | k1_xboole_0 = X1
% 3.38/0.99      | k1_xboole_0 = X0 ),
% 3.38/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_546,plain,
% 3.38/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.38/0.99      | ~ v1_relat_1(X2)
% 3.38/0.99      | ~ v1_funct_1(X2)
% 3.38/0.99      | X2 != X0
% 3.38/0.99      | k1_relat_1(X2) != X1
% 3.38/0.99      | k2_relat_1(X2) != k1_xboole_0
% 3.38/0.99      | k1_xboole_0 = X0
% 3.38/0.99      | k1_xboole_0 = X1 ),
% 3.38/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_31]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_547,plain,
% 3.38/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.38/0.99      | ~ v1_relat_1(X0)
% 3.38/0.99      | ~ v1_funct_1(X0)
% 3.38/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.38/0.99      | k1_xboole_0 = X0
% 3.38/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.38/0.99      inference(unflattening,[status(thm)],[c_546]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_563,plain,
% 3.38/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.38/0.99      | ~ v1_funct_1(X0)
% 3.38/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.38/0.99      | k1_xboole_0 = X0
% 3.38/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.38/0.99      inference(forward_subsumption_resolution,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_547,c_20]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1789,plain,
% 3.38/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.38/0.99      | k1_xboole_0 = X0
% 3.38/0.99      | k1_xboole_0 = k1_relat_1(X0)
% 3.38/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
% 3.38/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_563]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2002,plain,
% 3.38/0.99      ( k1_relat_1(X0) = k1_xboole_0
% 3.38/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.38/0.99      | k1_xboole_0 = X0
% 3.38/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.38/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.38/0.99      inference(demodulation,[status(thm)],[c_1789,c_9]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_6264,plain,
% 3.38/0.99      ( k1_relat_1(sK4) = k1_xboole_0
% 3.38/0.99      | sK3 != k1_xboole_0
% 3.38/0.99      | sK4 = k1_xboole_0
% 3.38/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.38/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_3183,c_2002]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2642,plain,
% 3.38/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4)) | r1_tarski(X0,sK4) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2643,plain,
% 3.38/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
% 3.38/0.99      | r1_tarski(X0,sK4) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_2642]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2645,plain,
% 3.38/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) != iProver_top
% 3.38/0.99      | r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_2643]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_6,plain,
% 3.38/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.38/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2703,plain,
% 3.38/0.99      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2704,plain,
% 3.38/0.99      ( sK4 = X0
% 3.38/0.99      | r1_tarski(X0,sK4) != iProver_top
% 3.38/0.99      | r1_tarski(sK4,X0) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_2703]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2706,plain,
% 3.38/0.99      ( sK4 = k1_xboole_0
% 3.38/0.99      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.38/0.99      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_2704]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3015,plain,
% 3.38/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) | r1_tarski(sK4,X0) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3016,plain,
% 3.38/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.38/0.99      | r1_tarski(sK4,X0) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_3015]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3018,plain,
% 3.38/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.38/0.99      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_3016]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_12,plain,
% 3.38/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.38/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3526,plain,
% 3.38/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3529,plain,
% 3.38/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_3526]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_6656,plain,
% 3.38/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.38/0.99      | sK4 = k1_xboole_0 ),
% 3.38/0.99      inference(global_propositional_subsumption,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_6264,c_2645,c_2706,c_3018,c_3529]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_6657,plain,
% 3.38/0.99      ( sK4 = k1_xboole_0
% 3.38/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.38/0.99      inference(renaming,[status(thm)],[c_6656]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_6662,plain,
% 3.38/0.99      ( sK4 = k1_xboole_0 | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_1805,c_6657]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_8557,plain,
% 3.38/0.99      ( sK4 = k1_xboole_0 ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_8244,c_6662]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_8157,plain,
% 3.38/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK4)))) = iProver_top ),
% 3.38/0.99      inference(demodulation,[status(thm)],[c_8154,c_7831]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_8340,plain,
% 3.38/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.38/0.99      inference(demodulation,[status(thm)],[c_8157,c_10]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_9628,plain,
% 3.38/0.99      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.38/0.99      inference(demodulation,[status(thm)],[c_8557,c_8340]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3580,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.38/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_10,c_1798]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_10129,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_9628,c_3580]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_8194,plain,
% 3.38/0.99      ( k1_relat_1(k2_funct_1(sK4)) = k1_xboole_0 ),
% 3.38/0.99      inference(demodulation,[status(thm)],[c_8154,c_3233]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_9626,plain,
% 3.38/0.99      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.38/0.99      inference(demodulation,[status(thm)],[c_8557,c_8194]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_10137,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.38/0.99      inference(light_normalisation,[status(thm)],[c_10129,c_9626]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_26,plain,
% 3.38/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.38/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.38/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.38/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_667,plain,
% 3.38/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.38/0.99      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.38/0.99      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.38/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.38/0.99      | k2_funct_1(sK4) != X0
% 3.38/0.99      | sK2 != X1
% 3.38/0.99      | sK3 != k1_xboole_0 ),
% 3.38/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_36]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_668,plain,
% 3.38/0.99      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.38/0.99      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 3.38/0.99      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.38/0.99      | k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.38/0.99      | sK3 != k1_xboole_0 ),
% 3.38/0.99      inference(unflattening,[status(thm)],[c_667]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_1784,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.38/0.99      | sK3 != k1_xboole_0
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 3.38/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2052,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.38/0.99      | sK3 != k1_xboole_0
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.38/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.38/0.99      inference(demodulation,[status(thm)],[c_1784,c_10]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2447,plain,
% 3.38/0.99      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.38/0.99      | sK3 != k1_xboole_0
% 3.38/0.99      | k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0 ),
% 3.38/0.99      inference(global_propositional_subsumption,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_2052,c_42,c_44,c_2168,c_2316]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2448,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.38/0.99      | sK3 != k1_xboole_0
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.38/0.99      inference(renaming,[status(thm)],[c_2447]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_8198,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.38/0.99      | k1_xboole_0 != k1_xboole_0
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.38/0.99      inference(demodulation,[status(thm)],[c_8154,c_2448]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_8235,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.38/0.99      inference(equality_resolution_simp,[status(thm)],[c_8198]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_8239,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 3.38/0.99      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.38/0.99      inference(demodulation,[status(thm)],[c_8235,c_10]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_8343,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0 ),
% 3.38/0.99      inference(backward_subsumption_resolution,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_8340,c_8239]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_10493,plain,
% 3.38/0.99      ( k1_relset_1(k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 3.38/0.99      inference(light_normalisation,[status(thm)],[c_8343,c_8557]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_11370,plain,
% 3.38/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.38/0.99      inference(demodulation,[status(thm)],[c_10137,c_10493]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_114,plain,
% 3.38/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_11,plain,
% 3.38/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.38/0.99      | k1_xboole_0 = X1
% 3.38/0.99      | k1_xboole_0 = X0 ),
% 3.38/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_113,plain,
% 3.38/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.38/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(contradiction,plain,
% 3.38/0.99      ( $false ),
% 3.38/0.99      inference(minisat,[status(thm)],[c_11370,c_114,c_113]) ).
% 3.38/0.99  
% 3.38/0.99  
% 3.38/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.38/0.99  
% 3.38/0.99  ------                               Statistics
% 3.38/0.99  
% 3.38/0.99  ------ General
% 3.38/0.99  
% 3.38/0.99  abstr_ref_over_cycles:                  0
% 3.38/0.99  abstr_ref_under_cycles:                 0
% 3.38/0.99  gc_basic_clause_elim:                   0
% 3.38/0.99  forced_gc_time:                         0
% 3.38/0.99  parsing_time:                           0.012
% 3.38/0.99  unif_index_cands_time:                  0.
% 3.38/0.99  unif_index_add_time:                    0.
% 3.38/0.99  orderings_time:                         0.
% 3.38/0.99  out_proof_time:                         0.016
% 3.38/0.99  total_time:                             0.29
% 3.38/0.99  num_of_symbols:                         52
% 3.38/0.99  num_of_terms:                           7674
% 3.38/0.99  
% 3.38/0.99  ------ Preprocessing
% 3.38/0.99  
% 3.38/0.99  num_of_splits:                          0
% 3.38/0.99  num_of_split_atoms:                     0
% 3.38/0.99  num_of_reused_defs:                     0
% 3.38/0.99  num_eq_ax_congr_red:                    11
% 3.38/0.99  num_of_sem_filtered_clauses:            1
% 3.38/0.99  num_of_subtypes:                        0
% 3.38/0.99  monotx_restored_types:                  0
% 3.38/0.99  sat_num_of_epr_types:                   0
% 3.38/0.99  sat_num_of_non_cyclic_types:            0
% 3.38/0.99  sat_guarded_non_collapsed_types:        0
% 3.38/0.99  num_pure_diseq_elim:                    0
% 3.38/0.99  simp_replaced_by:                       0
% 3.38/0.99  res_preprocessed:                       156
% 3.38/0.99  prep_upred:                             0
% 3.38/0.99  prep_unflattend:                        53
% 3.38/0.99  smt_new_axioms:                         0
% 3.38/0.99  pred_elim_cands:                        8
% 3.38/0.99  pred_elim:                              2
% 3.38/0.99  pred_elim_cl:                           -4
% 3.38/0.99  pred_elim_cycles:                       3
% 3.38/0.99  merged_defs:                            6
% 3.38/0.99  merged_defs_ncl:                        0
% 3.38/0.99  bin_hyper_res:                          6
% 3.38/0.99  prep_cycles:                            3
% 3.38/0.99  pred_elim_time:                         0.01
% 3.38/0.99  splitting_time:                         0.
% 3.38/0.99  sem_filter_time:                        0.
% 3.38/0.99  monotx_time:                            0.001
% 3.38/0.99  subtype_inf_time:                       0.
% 3.38/0.99  
% 3.38/0.99  ------ Problem properties
% 3.38/0.99  
% 3.38/0.99  clauses:                                43
% 3.38/0.99  conjectures:                            3
% 3.38/0.99  epr:                                    6
% 3.38/0.99  horn:                                   34
% 3.38/0.99  ground:                                 15
% 3.38/0.99  unary:                                  8
% 3.38/0.99  binary:                                 12
% 3.38/0.99  lits:                                   121
% 3.38/0.99  lits_eq:                                43
% 3.38/0.99  fd_pure:                                0
% 3.38/0.99  fd_pseudo:                              0
% 3.38/0.99  fd_cond:                                4
% 3.38/0.99  fd_pseudo_cond:                         1
% 3.38/0.99  ac_symbols:                             0
% 3.38/0.99  
% 3.38/0.99  ------ Propositional Solver
% 3.38/0.99  
% 3.38/0.99  prop_solver_calls:                      26
% 3.38/0.99  prop_fast_solver_calls:                 1539
% 3.38/0.99  smt_solver_calls:                       0
% 3.38/0.99  smt_fast_solver_calls:                  0
% 3.38/0.99  prop_num_of_clauses:                    3834
% 3.38/0.99  prop_preprocess_simplified:             10199
% 3.38/0.99  prop_fo_subsumed:                       86
% 3.38/0.99  prop_solver_time:                       0.
% 3.38/0.99  smt_solver_time:                        0.
% 3.38/0.99  smt_fast_solver_time:                   0.
% 3.38/0.99  prop_fast_solver_time:                  0.
% 3.38/0.99  prop_unsat_core_time:                   0.
% 3.38/0.99  
% 3.38/0.99  ------ QBF
% 3.38/0.99  
% 3.38/0.99  qbf_q_res:                              0
% 3.38/0.99  qbf_num_tautologies:                    0
% 3.38/0.99  qbf_prep_cycles:                        0
% 3.38/0.99  
% 3.38/0.99  ------ BMC1
% 3.38/0.99  
% 3.38/0.99  bmc1_current_bound:                     -1
% 3.38/0.99  bmc1_last_solved_bound:                 -1
% 3.38/0.99  bmc1_unsat_core_size:                   -1
% 3.38/0.99  bmc1_unsat_core_parents_size:           -1
% 3.38/0.99  bmc1_merge_next_fun:                    0
% 3.38/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.38/0.99  
% 3.38/0.99  ------ Instantiation
% 3.38/0.99  
% 3.38/0.99  inst_num_of_clauses:                    1203
% 3.38/0.99  inst_num_in_passive:                    480
% 3.38/0.99  inst_num_in_active:                     507
% 3.38/0.99  inst_num_in_unprocessed:                218
% 3.38/0.99  inst_num_of_loops:                      830
% 3.38/0.99  inst_num_of_learning_restarts:          0
% 3.38/0.99  inst_num_moves_active_passive:          319
% 3.38/0.99  inst_lit_activity:                      0
% 3.38/0.99  inst_lit_activity_moves:                0
% 3.38/0.99  inst_num_tautologies:                   0
% 3.38/0.99  inst_num_prop_implied:                  0
% 3.38/0.99  inst_num_existing_simplified:           0
% 3.38/0.99  inst_num_eq_res_simplified:             0
% 3.38/0.99  inst_num_child_elim:                    0
% 3.38/0.99  inst_num_of_dismatching_blockings:      436
% 3.38/0.99  inst_num_of_non_proper_insts:           1273
% 3.38/0.99  inst_num_of_duplicates:                 0
% 3.38/0.99  inst_inst_num_from_inst_to_res:         0
% 3.38/0.99  inst_dismatching_checking_time:         0.
% 3.38/0.99  
% 3.38/0.99  ------ Resolution
% 3.38/0.99  
% 3.38/0.99  res_num_of_clauses:                     0
% 3.38/0.99  res_num_in_passive:                     0
% 3.38/0.99  res_num_in_active:                      0
% 3.38/0.99  res_num_of_loops:                       159
% 3.38/0.99  res_forward_subset_subsumed:            89
% 3.38/0.99  res_backward_subset_subsumed:           4
% 3.38/0.99  res_forward_subsumed:                   0
% 3.38/0.99  res_backward_subsumed:                  0
% 3.38/0.99  res_forward_subsumption_resolution:     7
% 3.38/0.99  res_backward_subsumption_resolution:    0
% 3.38/0.99  res_clause_to_clause_subsumption:       753
% 3.38/0.99  res_orphan_elimination:                 0
% 3.38/0.99  res_tautology_del:                      80
% 3.38/0.99  res_num_eq_res_simplified:              0
% 3.38/0.99  res_num_sel_changes:                    0
% 3.38/0.99  res_moves_from_active_to_pass:          0
% 3.38/0.99  
% 3.38/0.99  ------ Superposition
% 3.38/0.99  
% 3.38/0.99  sup_time_total:                         0.
% 3.38/0.99  sup_time_generating:                    0.
% 3.38/0.99  sup_time_sim_full:                      0.
% 3.38/0.99  sup_time_sim_immed:                     0.
% 3.38/0.99  
% 3.38/0.99  sup_num_of_clauses:                     143
% 3.38/0.99  sup_num_in_active:                      76
% 3.38/0.99  sup_num_in_passive:                     67
% 3.38/0.99  sup_num_of_loops:                       164
% 3.38/0.99  sup_fw_superposition:                   166
% 3.38/0.99  sup_bw_superposition:                   139
% 3.38/0.99  sup_immediate_simplified:               127
% 3.38/0.99  sup_given_eliminated:                   1
% 3.38/0.99  comparisons_done:                       0
% 3.38/0.99  comparisons_avoided:                    24
% 3.38/0.99  
% 3.38/0.99  ------ Simplifications
% 3.38/0.99  
% 3.38/0.99  
% 3.38/0.99  sim_fw_subset_subsumed:                 37
% 3.38/0.99  sim_bw_subset_subsumed:                 31
% 3.38/0.99  sim_fw_subsumed:                        25
% 3.38/0.99  sim_bw_subsumed:                        10
% 3.38/0.99  sim_fw_subsumption_res:                 1
% 3.38/0.99  sim_bw_subsumption_res:                 3
% 3.38/0.99  sim_tautology_del:                      9
% 3.38/0.99  sim_eq_tautology_del:                   25
% 3.38/0.99  sim_eq_res_simp:                        4
% 3.38/0.99  sim_fw_demodulated:                     39
% 3.38/0.99  sim_bw_demodulated:                     78
% 3.38/0.99  sim_light_normalised:                   84
% 3.38/0.99  sim_joinable_taut:                      0
% 3.38/0.99  sim_joinable_simp:                      0
% 3.38/0.99  sim_ac_normalised:                      0
% 3.38/0.99  sim_smt_subsumption:                    0
% 3.38/0.99  
%------------------------------------------------------------------------------
