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
% DateTime   : Thu Dec  3 12:02:33 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  156 (4545 expanded)
%              Number of clauses        :  100 (1561 expanded)
%              Number of leaves         :   13 ( 853 expanded)
%              Depth                    :   24
%              Number of atoms          :  492 (23447 expanded)
%              Number of equality atoms :  242 (4815 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

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
    inference(ennf_transformation,[],[f21])).

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
    inference(flattening,[],[f40])).

fof(f57,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
        | ~ v1_funct_1(k2_funct_1(sK6)) )
      & k2_relset_1(sK4,sK5,sK6) = sK5
      & v2_funct_1(sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
      | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
      | ~ v1_funct_1(k2_funct_1(sK6)) )
    & k2_relset_1(sK4,sK5,sK6) = sK5
    & v2_funct_1(sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f41,f57])).

fof(f99,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f100,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f58])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f79,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f101,plain,(
    v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f58])).

fof(f98,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f58])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f102,plain,(
    k2_relset_1(sK4,sK5,sK6) = sK5 ),
    inference(cnf_transformation,[],[f58])).

fof(f78,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f77,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f103,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
    | ~ v1_funct_1(k2_funct_1(sK6)) ),
    inference(cnf_transformation,[],[f58])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f105,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f65])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_739,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X1
    | sK5 != X2
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_43])).

cnf(c_740,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_739])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_742,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_740,c_42])).

cnf(c_1539,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1543,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4171,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1539,c_1543])).

cnf(c_4301,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_742,c_4171])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1544,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2725,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_1544])).

cnf(c_19,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_41,negated_conjecture,
    ( v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_486,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_41])).

cnf(c_487,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_489,plain,
    ( ~ v1_relat_1(sK6)
    | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_487,c_44])).

cnf(c_1535,plain,
    ( k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6)
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_2799,plain,
    ( k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2725,c_1535])).

cnf(c_33,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1540,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4583,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK6)),k1_relat_1(sK6)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK6)) != iProver_top
    | v1_relat_1(k2_funct_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2799,c_1540])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1542,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3456,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1539,c_1542])).

cnf(c_40,negated_conjecture,
    ( k2_relset_1(sK4,sK5,sK6) = sK5 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3468,plain,
    ( k2_relat_1(sK6) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_3456,c_40])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_472,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_41])).

cnf(c_473,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_475,plain,
    ( ~ v1_relat_1(sK6)
    | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_44])).

cnf(c_1536,plain,
    ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6)
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_475])).

cnf(c_2798,plain,
    ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2725,c_1536])).

cnf(c_3539,plain,
    ( k1_relat_1(k2_funct_1(sK6)) = sK5 ),
    inference(demodulation,[status(thm)],[c_3468,c_2798])).

cnf(c_4596,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK6)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK6)) != iProver_top
    | v1_relat_1(k2_funct_1(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4583,c_3539])).

cnf(c_45,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_47,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_17,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1898,plain,
    ( v1_funct_1(k2_funct_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1899,plain,
    ( v1_funct_1(k2_funct_1(sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1898])).

cnf(c_1907,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2052,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1907])).

cnf(c_2053,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2052])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4992,plain,
    ( ~ v1_funct_1(sK6)
    | v1_relat_1(k2_funct_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_4993,plain,
    ( v1_funct_1(sK6) != iProver_top
    | v1_relat_1(k2_funct_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4992])).

cnf(c_5075,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK6)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4596,c_45,c_47,c_1899,c_2053,c_4993])).

cnf(c_5083,plain,
    ( k1_relset_1(sK5,k1_relat_1(sK6),k2_funct_1(sK6)) = k1_relat_1(k2_funct_1(sK6)) ),
    inference(superposition,[status(thm)],[c_5075,c_1543])).

cnf(c_5089,plain,
    ( k1_relset_1(sK5,k1_relat_1(sK6),k2_funct_1(sK6)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_5083,c_3539])).

cnf(c_5105,plain,
    ( k1_relset_1(sK5,sK4,k2_funct_1(sK6)) = sK5
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4301,c_5089])).

cnf(c_34,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_39,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
    | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(k2_funct_1(sK6)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_750,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK6))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK6) != X0
    | k1_relat_1(X0) != sK5
    | k2_relat_1(X0) != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_39])).

cnf(c_751,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | k1_relat_1(k2_funct_1(sK6)) != sK5
    | k2_relat_1(k2_funct_1(sK6)) != sK4 ),
    inference(unflattening,[status(thm)],[c_750])).

cnf(c_763,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | k1_relat_1(k2_funct_1(sK6)) != sK5
    | k2_relat_1(k2_funct_1(sK6)) != sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_751,c_23])).

cnf(c_1524,plain,
    ( k1_relat_1(k2_funct_1(sK6)) != sK5
    | k2_relat_1(k2_funct_1(sK6)) != sK4
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_768,plain,
    ( k1_relat_1(k2_funct_1(sK6)) != sK5
    | k2_relat_1(k2_funct_1(sK6)) != sK4
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_2162,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | k2_relat_1(k2_funct_1(sK6)) != sK4
    | k1_relat_1(k2_funct_1(sK6)) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1524,c_45,c_47,c_768,c_1899,c_2053])).

cnf(c_2163,plain,
    ( k1_relat_1(k2_funct_1(sK6)) != sK5
    | k2_relat_1(k2_funct_1(sK6)) != sK4
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2162])).

cnf(c_2805,plain,
    ( k2_relat_1(k2_funct_1(sK6)) != sK4
    | k2_relat_1(sK6) != sK5
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2798,c_2163])).

cnf(c_2867,plain,
    ( k1_relat_1(sK6) != sK4
    | k2_relat_1(sK6) != sK5
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2805,c_2799])).

cnf(c_3538,plain,
    ( k1_relat_1(sK6) != sK4
    | sK5 != sK5
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3468,c_2867])).

cnf(c_3542,plain,
    ( k1_relat_1(sK6) != sK4
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3538])).

cnf(c_4350,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4301,c_3542])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_37,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_426,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_37])).

cnf(c_427,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_769,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK6))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK6) != X0
    | k1_relat_1(X0) != sK5
    | k2_relat_1(X0) != k1_xboole_0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_427,c_39])).

cnf(c_770,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | k1_relat_1(k2_funct_1(sK6)) != sK5
    | k2_relat_1(k2_funct_1(sK6)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_769])).

cnf(c_782,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | k1_relat_1(k2_funct_1(sK6)) != sK5
    | k2_relat_1(k2_funct_1(sK6)) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_770,c_23])).

cnf(c_1523,plain,
    ( k1_relat_1(k2_funct_1(sK6)) != sK5
    | k2_relat_1(k2_funct_1(sK6)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_2806,plain,
    ( k2_relat_1(k2_funct_1(sK6)) != k1_xboole_0
    | k2_relat_1(sK6) != sK5
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2798,c_1523])).

cnf(c_3225,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | k2_relat_1(sK6) != sK5
    | k2_relat_1(k2_funct_1(sK6)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2806,c_45,c_47,c_1899,c_2053])).

cnf(c_3226,plain,
    ( k2_relat_1(k2_funct_1(sK6)) != k1_xboole_0
    | k2_relat_1(sK6) != sK5
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3225])).

cnf(c_3229,plain,
    ( k1_relat_1(sK6) != k1_xboole_0
    | k2_relat_1(sK6) != sK5
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3226,c_2799])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1550,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3572,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | sK5 != k1_xboole_0
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3468,c_1550])).

cnf(c_3808,plain,
    ( sK5 != k1_xboole_0
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3572,c_47,c_2053])).

cnf(c_3809,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3808])).

cnf(c_4451,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4350,c_3229,c_3468,c_3809])).

cnf(c_5080,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4301,c_5075])).

cnf(c_5128,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5105,c_3229,c_3468,c_3809,c_4350,c_5080])).

cnf(c_5132,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK6)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5128,c_5075])).

cnf(c_5147,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5128,c_3809])).

cnf(c_5209,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5147])).

cnf(c_5265,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5132,c_5209])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_5267,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5265,c_6])).

cnf(c_3535,plain,
    ( k1_relat_1(sK6) != k1_xboole_0
    | sK5 != sK5
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3468,c_3229])).

cnf(c_3555,plain,
    ( k1_relat_1(sK6) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3535])).

cnf(c_5143,plain,
    ( k1_relat_1(sK6) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5128,c_3555])).

cnf(c_5231,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5143,c_5209])).

cnf(c_5232,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5231])).

cnf(c_5234,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5232,c_6])).

cnf(c_5269,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5267,c_5234])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:25:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.02/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.00  
% 3.02/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.02/1.00  
% 3.02/1.00  ------  iProver source info
% 3.02/1.00  
% 3.02/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.02/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.02/1.00  git: non_committed_changes: false
% 3.02/1.00  git: last_make_outside_of_git: false
% 3.02/1.00  
% 3.02/1.00  ------ 
% 3.02/1.00  
% 3.02/1.00  ------ Input Options
% 3.02/1.00  
% 3.02/1.00  --out_options                           all
% 3.02/1.00  --tptp_safe_out                         true
% 3.02/1.00  --problem_path                          ""
% 3.02/1.00  --include_path                          ""
% 3.02/1.00  --clausifier                            res/vclausify_rel
% 3.02/1.00  --clausifier_options                    --mode clausify
% 3.02/1.00  --stdin                                 false
% 3.02/1.00  --stats_out                             all
% 3.02/1.00  
% 3.02/1.00  ------ General Options
% 3.02/1.00  
% 3.02/1.00  --fof                                   false
% 3.02/1.00  --time_out_real                         305.
% 3.02/1.00  --time_out_virtual                      -1.
% 3.02/1.00  --symbol_type_check                     false
% 3.02/1.00  --clausify_out                          false
% 3.02/1.00  --sig_cnt_out                           false
% 3.02/1.00  --trig_cnt_out                          false
% 3.02/1.00  --trig_cnt_out_tolerance                1.
% 3.02/1.00  --trig_cnt_out_sk_spl                   false
% 3.02/1.00  --abstr_cl_out                          false
% 3.02/1.00  
% 3.02/1.00  ------ Global Options
% 3.02/1.00  
% 3.02/1.00  --schedule                              default
% 3.02/1.00  --add_important_lit                     false
% 3.02/1.00  --prop_solver_per_cl                    1000
% 3.02/1.00  --min_unsat_core                        false
% 3.02/1.00  --soft_assumptions                      false
% 3.02/1.00  --soft_lemma_size                       3
% 3.02/1.00  --prop_impl_unit_size                   0
% 3.02/1.00  --prop_impl_unit                        []
% 3.02/1.00  --share_sel_clauses                     true
% 3.02/1.00  --reset_solvers                         false
% 3.02/1.00  --bc_imp_inh                            [conj_cone]
% 3.02/1.00  --conj_cone_tolerance                   3.
% 3.02/1.00  --extra_neg_conj                        none
% 3.02/1.00  --large_theory_mode                     true
% 3.02/1.00  --prolific_symb_bound                   200
% 3.02/1.00  --lt_threshold                          2000
% 3.02/1.00  --clause_weak_htbl                      true
% 3.02/1.00  --gc_record_bc_elim                     false
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing Options
% 3.02/1.00  
% 3.02/1.00  --preprocessing_flag                    true
% 3.02/1.00  --time_out_prep_mult                    0.1
% 3.02/1.00  --splitting_mode                        input
% 3.02/1.00  --splitting_grd                         true
% 3.02/1.00  --splitting_cvd                         false
% 3.02/1.00  --splitting_cvd_svl                     false
% 3.02/1.00  --splitting_nvd                         32
% 3.02/1.00  --sub_typing                            true
% 3.02/1.00  --prep_gs_sim                           true
% 3.02/1.00  --prep_unflatten                        true
% 3.02/1.00  --prep_res_sim                          true
% 3.02/1.00  --prep_upred                            true
% 3.02/1.00  --prep_sem_filter                       exhaustive
% 3.02/1.00  --prep_sem_filter_out                   false
% 3.02/1.00  --pred_elim                             true
% 3.02/1.00  --res_sim_input                         true
% 3.02/1.00  --eq_ax_congr_red                       true
% 3.02/1.00  --pure_diseq_elim                       true
% 3.02/1.00  --brand_transform                       false
% 3.02/1.00  --non_eq_to_eq                          false
% 3.02/1.00  --prep_def_merge                        true
% 3.02/1.00  --prep_def_merge_prop_impl              false
% 3.02/1.00  --prep_def_merge_mbd                    true
% 3.02/1.00  --prep_def_merge_tr_red                 false
% 3.02/1.00  --prep_def_merge_tr_cl                  false
% 3.02/1.00  --smt_preprocessing                     true
% 3.02/1.00  --smt_ac_axioms                         fast
% 3.02/1.00  --preprocessed_out                      false
% 3.02/1.00  --preprocessed_stats                    false
% 3.02/1.00  
% 3.02/1.00  ------ Abstraction refinement Options
% 3.02/1.00  
% 3.02/1.00  --abstr_ref                             []
% 3.02/1.00  --abstr_ref_prep                        false
% 3.02/1.00  --abstr_ref_until_sat                   false
% 3.02/1.00  --abstr_ref_sig_restrict                funpre
% 3.02/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/1.00  --abstr_ref_under                       []
% 3.02/1.00  
% 3.02/1.00  ------ SAT Options
% 3.02/1.00  
% 3.02/1.00  --sat_mode                              false
% 3.02/1.00  --sat_fm_restart_options                ""
% 3.02/1.00  --sat_gr_def                            false
% 3.02/1.00  --sat_epr_types                         true
% 3.02/1.00  --sat_non_cyclic_types                  false
% 3.02/1.00  --sat_finite_models                     false
% 3.02/1.00  --sat_fm_lemmas                         false
% 3.02/1.00  --sat_fm_prep                           false
% 3.02/1.00  --sat_fm_uc_incr                        true
% 3.02/1.00  --sat_out_model                         small
% 3.02/1.00  --sat_out_clauses                       false
% 3.02/1.00  
% 3.02/1.00  ------ QBF Options
% 3.02/1.00  
% 3.02/1.00  --qbf_mode                              false
% 3.02/1.00  --qbf_elim_univ                         false
% 3.02/1.00  --qbf_dom_inst                          none
% 3.02/1.00  --qbf_dom_pre_inst                      false
% 3.02/1.00  --qbf_sk_in                             false
% 3.02/1.00  --qbf_pred_elim                         true
% 3.02/1.00  --qbf_split                             512
% 3.02/1.00  
% 3.02/1.00  ------ BMC1 Options
% 3.02/1.00  
% 3.02/1.00  --bmc1_incremental                      false
% 3.02/1.00  --bmc1_axioms                           reachable_all
% 3.02/1.00  --bmc1_min_bound                        0
% 3.02/1.00  --bmc1_max_bound                        -1
% 3.02/1.00  --bmc1_max_bound_default                -1
% 3.02/1.00  --bmc1_symbol_reachability              true
% 3.02/1.00  --bmc1_property_lemmas                  false
% 3.02/1.00  --bmc1_k_induction                      false
% 3.02/1.00  --bmc1_non_equiv_states                 false
% 3.02/1.00  --bmc1_deadlock                         false
% 3.02/1.00  --bmc1_ucm                              false
% 3.02/1.00  --bmc1_add_unsat_core                   none
% 3.02/1.00  --bmc1_unsat_core_children              false
% 3.02/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/1.00  --bmc1_out_stat                         full
% 3.02/1.00  --bmc1_ground_init                      false
% 3.02/1.00  --bmc1_pre_inst_next_state              false
% 3.02/1.00  --bmc1_pre_inst_state                   false
% 3.02/1.00  --bmc1_pre_inst_reach_state             false
% 3.02/1.00  --bmc1_out_unsat_core                   false
% 3.02/1.00  --bmc1_aig_witness_out                  false
% 3.02/1.00  --bmc1_verbose                          false
% 3.02/1.00  --bmc1_dump_clauses_tptp                false
% 3.02/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.02/1.00  --bmc1_dump_file                        -
% 3.02/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.02/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.02/1.00  --bmc1_ucm_extend_mode                  1
% 3.02/1.00  --bmc1_ucm_init_mode                    2
% 3.02/1.00  --bmc1_ucm_cone_mode                    none
% 3.02/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.02/1.00  --bmc1_ucm_relax_model                  4
% 3.02/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.02/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/1.00  --bmc1_ucm_layered_model                none
% 3.02/1.00  --bmc1_ucm_max_lemma_size               10
% 3.02/1.00  
% 3.02/1.00  ------ AIG Options
% 3.02/1.00  
% 3.02/1.00  --aig_mode                              false
% 3.02/1.00  
% 3.02/1.00  ------ Instantiation Options
% 3.02/1.00  
% 3.02/1.00  --instantiation_flag                    true
% 3.02/1.00  --inst_sos_flag                         false
% 3.02/1.00  --inst_sos_phase                        true
% 3.02/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/1.00  --inst_lit_sel_side                     num_symb
% 3.02/1.00  --inst_solver_per_active                1400
% 3.02/1.00  --inst_solver_calls_frac                1.
% 3.02/1.00  --inst_passive_queue_type               priority_queues
% 3.02/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/1.00  --inst_passive_queues_freq              [25;2]
% 3.02/1.00  --inst_dismatching                      true
% 3.02/1.00  --inst_eager_unprocessed_to_passive     true
% 3.02/1.00  --inst_prop_sim_given                   true
% 3.02/1.00  --inst_prop_sim_new                     false
% 3.02/1.00  --inst_subs_new                         false
% 3.02/1.00  --inst_eq_res_simp                      false
% 3.02/1.00  --inst_subs_given                       false
% 3.02/1.00  --inst_orphan_elimination               true
% 3.02/1.00  --inst_learning_loop_flag               true
% 3.02/1.00  --inst_learning_start                   3000
% 3.02/1.00  --inst_learning_factor                  2
% 3.02/1.00  --inst_start_prop_sim_after_learn       3
% 3.02/1.00  --inst_sel_renew                        solver
% 3.02/1.00  --inst_lit_activity_flag                true
% 3.02/1.00  --inst_restr_to_given                   false
% 3.02/1.00  --inst_activity_threshold               500
% 3.02/1.00  --inst_out_proof                        true
% 3.02/1.00  
% 3.02/1.00  ------ Resolution Options
% 3.02/1.00  
% 3.02/1.00  --resolution_flag                       true
% 3.02/1.00  --res_lit_sel                           adaptive
% 3.02/1.00  --res_lit_sel_side                      none
% 3.02/1.00  --res_ordering                          kbo
% 3.02/1.00  --res_to_prop_solver                    active
% 3.02/1.00  --res_prop_simpl_new                    false
% 3.02/1.00  --res_prop_simpl_given                  true
% 3.02/1.00  --res_passive_queue_type                priority_queues
% 3.02/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/1.00  --res_passive_queues_freq               [15;5]
% 3.02/1.00  --res_forward_subs                      full
% 3.02/1.00  --res_backward_subs                     full
% 3.02/1.00  --res_forward_subs_resolution           true
% 3.02/1.00  --res_backward_subs_resolution          true
% 3.02/1.00  --res_orphan_elimination                true
% 3.02/1.00  --res_time_limit                        2.
% 3.02/1.00  --res_out_proof                         true
% 3.02/1.00  
% 3.02/1.00  ------ Superposition Options
% 3.02/1.00  
% 3.02/1.00  --superposition_flag                    true
% 3.02/1.00  --sup_passive_queue_type                priority_queues
% 3.02/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.02/1.00  --demod_completeness_check              fast
% 3.02/1.00  --demod_use_ground                      true
% 3.02/1.00  --sup_to_prop_solver                    passive
% 3.02/1.00  --sup_prop_simpl_new                    true
% 3.02/1.00  --sup_prop_simpl_given                  true
% 3.02/1.00  --sup_fun_splitting                     false
% 3.02/1.00  --sup_smt_interval                      50000
% 3.02/1.00  
% 3.02/1.00  ------ Superposition Simplification Setup
% 3.02/1.00  
% 3.02/1.00  --sup_indices_passive                   []
% 3.02/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.00  --sup_full_bw                           [BwDemod]
% 3.02/1.00  --sup_immed_triv                        [TrivRules]
% 3.02/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.00  --sup_immed_bw_main                     []
% 3.02/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.00  
% 3.02/1.00  ------ Combination Options
% 3.02/1.00  
% 3.02/1.00  --comb_res_mult                         3
% 3.02/1.00  --comb_sup_mult                         2
% 3.02/1.00  --comb_inst_mult                        10
% 3.02/1.00  
% 3.02/1.00  ------ Debug Options
% 3.02/1.00  
% 3.02/1.00  --dbg_backtrace                         false
% 3.02/1.00  --dbg_dump_prop_clauses                 false
% 3.02/1.00  --dbg_dump_prop_clauses_file            -
% 3.02/1.00  --dbg_out_stat                          false
% 3.02/1.00  ------ Parsing...
% 3.02/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.02/1.00  ------ Proving...
% 3.02/1.00  ------ Problem Properties 
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  clauses                                 45
% 3.02/1.00  conjectures                             3
% 3.02/1.00  EPR                                     6
% 3.02/1.00  Horn                                    37
% 3.02/1.00  unary                                   11
% 3.02/1.00  binary                                  11
% 3.02/1.00  lits                                    120
% 3.02/1.00  lits eq                                 52
% 3.02/1.00  fd_pure                                 0
% 3.02/1.00  fd_pseudo                               0
% 3.02/1.00  fd_cond                                 4
% 3.02/1.00  fd_pseudo_cond                          2
% 3.02/1.00  AC symbols                              0
% 3.02/1.00  
% 3.02/1.00  ------ Schedule dynamic 5 is on 
% 3.02/1.00  
% 3.02/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  ------ 
% 3.02/1.00  Current options:
% 3.02/1.00  ------ 
% 3.02/1.00  
% 3.02/1.00  ------ Input Options
% 3.02/1.00  
% 3.02/1.00  --out_options                           all
% 3.02/1.00  --tptp_safe_out                         true
% 3.02/1.00  --problem_path                          ""
% 3.02/1.00  --include_path                          ""
% 3.02/1.00  --clausifier                            res/vclausify_rel
% 3.02/1.00  --clausifier_options                    --mode clausify
% 3.02/1.00  --stdin                                 false
% 3.02/1.00  --stats_out                             all
% 3.02/1.00  
% 3.02/1.00  ------ General Options
% 3.02/1.00  
% 3.02/1.00  --fof                                   false
% 3.02/1.00  --time_out_real                         305.
% 3.02/1.00  --time_out_virtual                      -1.
% 3.02/1.00  --symbol_type_check                     false
% 3.02/1.00  --clausify_out                          false
% 3.02/1.00  --sig_cnt_out                           false
% 3.02/1.00  --trig_cnt_out                          false
% 3.02/1.00  --trig_cnt_out_tolerance                1.
% 3.02/1.00  --trig_cnt_out_sk_spl                   false
% 3.02/1.00  --abstr_cl_out                          false
% 3.02/1.00  
% 3.02/1.00  ------ Global Options
% 3.02/1.00  
% 3.02/1.00  --schedule                              default
% 3.02/1.00  --add_important_lit                     false
% 3.02/1.00  --prop_solver_per_cl                    1000
% 3.02/1.00  --min_unsat_core                        false
% 3.02/1.00  --soft_assumptions                      false
% 3.02/1.00  --soft_lemma_size                       3
% 3.02/1.00  --prop_impl_unit_size                   0
% 3.02/1.00  --prop_impl_unit                        []
% 3.02/1.00  --share_sel_clauses                     true
% 3.02/1.00  --reset_solvers                         false
% 3.02/1.00  --bc_imp_inh                            [conj_cone]
% 3.02/1.00  --conj_cone_tolerance                   3.
% 3.02/1.00  --extra_neg_conj                        none
% 3.02/1.00  --large_theory_mode                     true
% 3.02/1.00  --prolific_symb_bound                   200
% 3.02/1.00  --lt_threshold                          2000
% 3.02/1.00  --clause_weak_htbl                      true
% 3.02/1.00  --gc_record_bc_elim                     false
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing Options
% 3.02/1.00  
% 3.02/1.00  --preprocessing_flag                    true
% 3.02/1.00  --time_out_prep_mult                    0.1
% 3.02/1.00  --splitting_mode                        input
% 3.02/1.00  --splitting_grd                         true
% 3.02/1.00  --splitting_cvd                         false
% 3.02/1.00  --splitting_cvd_svl                     false
% 3.02/1.00  --splitting_nvd                         32
% 3.02/1.00  --sub_typing                            true
% 3.02/1.00  --prep_gs_sim                           true
% 3.02/1.00  --prep_unflatten                        true
% 3.02/1.00  --prep_res_sim                          true
% 3.02/1.00  --prep_upred                            true
% 3.02/1.00  --prep_sem_filter                       exhaustive
% 3.02/1.00  --prep_sem_filter_out                   false
% 3.02/1.00  --pred_elim                             true
% 3.02/1.00  --res_sim_input                         true
% 3.02/1.00  --eq_ax_congr_red                       true
% 3.02/1.00  --pure_diseq_elim                       true
% 3.02/1.00  --brand_transform                       false
% 3.02/1.00  --non_eq_to_eq                          false
% 3.02/1.00  --prep_def_merge                        true
% 3.02/1.00  --prep_def_merge_prop_impl              false
% 3.02/1.00  --prep_def_merge_mbd                    true
% 3.02/1.00  --prep_def_merge_tr_red                 false
% 3.02/1.00  --prep_def_merge_tr_cl                  false
% 3.02/1.00  --smt_preprocessing                     true
% 3.02/1.00  --smt_ac_axioms                         fast
% 3.02/1.00  --preprocessed_out                      false
% 3.02/1.00  --preprocessed_stats                    false
% 3.02/1.00  
% 3.02/1.00  ------ Abstraction refinement Options
% 3.02/1.00  
% 3.02/1.00  --abstr_ref                             []
% 3.02/1.00  --abstr_ref_prep                        false
% 3.02/1.00  --abstr_ref_until_sat                   false
% 3.02/1.00  --abstr_ref_sig_restrict                funpre
% 3.02/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/1.00  --abstr_ref_under                       []
% 3.02/1.00  
% 3.02/1.00  ------ SAT Options
% 3.02/1.00  
% 3.02/1.00  --sat_mode                              false
% 3.02/1.00  --sat_fm_restart_options                ""
% 3.02/1.00  --sat_gr_def                            false
% 3.02/1.00  --sat_epr_types                         true
% 3.02/1.00  --sat_non_cyclic_types                  false
% 3.02/1.00  --sat_finite_models                     false
% 3.02/1.00  --sat_fm_lemmas                         false
% 3.02/1.00  --sat_fm_prep                           false
% 3.02/1.00  --sat_fm_uc_incr                        true
% 3.02/1.00  --sat_out_model                         small
% 3.02/1.00  --sat_out_clauses                       false
% 3.02/1.00  
% 3.02/1.00  ------ QBF Options
% 3.02/1.00  
% 3.02/1.00  --qbf_mode                              false
% 3.02/1.00  --qbf_elim_univ                         false
% 3.02/1.00  --qbf_dom_inst                          none
% 3.02/1.00  --qbf_dom_pre_inst                      false
% 3.02/1.00  --qbf_sk_in                             false
% 3.02/1.00  --qbf_pred_elim                         true
% 3.02/1.00  --qbf_split                             512
% 3.02/1.00  
% 3.02/1.00  ------ BMC1 Options
% 3.02/1.00  
% 3.02/1.00  --bmc1_incremental                      false
% 3.02/1.00  --bmc1_axioms                           reachable_all
% 3.02/1.00  --bmc1_min_bound                        0
% 3.02/1.00  --bmc1_max_bound                        -1
% 3.02/1.00  --bmc1_max_bound_default                -1
% 3.02/1.00  --bmc1_symbol_reachability              true
% 3.02/1.00  --bmc1_property_lemmas                  false
% 3.02/1.00  --bmc1_k_induction                      false
% 3.02/1.00  --bmc1_non_equiv_states                 false
% 3.02/1.00  --bmc1_deadlock                         false
% 3.02/1.00  --bmc1_ucm                              false
% 3.02/1.00  --bmc1_add_unsat_core                   none
% 3.02/1.00  --bmc1_unsat_core_children              false
% 3.02/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/1.00  --bmc1_out_stat                         full
% 3.02/1.00  --bmc1_ground_init                      false
% 3.02/1.00  --bmc1_pre_inst_next_state              false
% 3.02/1.00  --bmc1_pre_inst_state                   false
% 3.02/1.00  --bmc1_pre_inst_reach_state             false
% 3.02/1.00  --bmc1_out_unsat_core                   false
% 3.02/1.00  --bmc1_aig_witness_out                  false
% 3.02/1.00  --bmc1_verbose                          false
% 3.02/1.00  --bmc1_dump_clauses_tptp                false
% 3.02/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.02/1.00  --bmc1_dump_file                        -
% 3.02/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.02/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.02/1.00  --bmc1_ucm_extend_mode                  1
% 3.02/1.00  --bmc1_ucm_init_mode                    2
% 3.02/1.00  --bmc1_ucm_cone_mode                    none
% 3.02/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.02/1.00  --bmc1_ucm_relax_model                  4
% 3.02/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.02/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/1.00  --bmc1_ucm_layered_model                none
% 3.02/1.00  --bmc1_ucm_max_lemma_size               10
% 3.02/1.00  
% 3.02/1.00  ------ AIG Options
% 3.02/1.00  
% 3.02/1.00  --aig_mode                              false
% 3.02/1.00  
% 3.02/1.00  ------ Instantiation Options
% 3.02/1.00  
% 3.02/1.00  --instantiation_flag                    true
% 3.02/1.00  --inst_sos_flag                         false
% 3.02/1.00  --inst_sos_phase                        true
% 3.02/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/1.00  --inst_lit_sel_side                     none
% 3.02/1.00  --inst_solver_per_active                1400
% 3.02/1.00  --inst_solver_calls_frac                1.
% 3.02/1.00  --inst_passive_queue_type               priority_queues
% 3.02/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/1.00  --inst_passive_queues_freq              [25;2]
% 3.02/1.00  --inst_dismatching                      true
% 3.02/1.00  --inst_eager_unprocessed_to_passive     true
% 3.02/1.00  --inst_prop_sim_given                   true
% 3.02/1.00  --inst_prop_sim_new                     false
% 3.02/1.00  --inst_subs_new                         false
% 3.02/1.00  --inst_eq_res_simp                      false
% 3.02/1.00  --inst_subs_given                       false
% 3.02/1.00  --inst_orphan_elimination               true
% 3.02/1.00  --inst_learning_loop_flag               true
% 3.02/1.00  --inst_learning_start                   3000
% 3.02/1.00  --inst_learning_factor                  2
% 3.02/1.00  --inst_start_prop_sim_after_learn       3
% 3.02/1.00  --inst_sel_renew                        solver
% 3.02/1.00  --inst_lit_activity_flag                true
% 3.02/1.00  --inst_restr_to_given                   false
% 3.02/1.00  --inst_activity_threshold               500
% 3.02/1.00  --inst_out_proof                        true
% 3.02/1.00  
% 3.02/1.00  ------ Resolution Options
% 3.02/1.00  
% 3.02/1.00  --resolution_flag                       false
% 3.02/1.00  --res_lit_sel                           adaptive
% 3.02/1.00  --res_lit_sel_side                      none
% 3.02/1.00  --res_ordering                          kbo
% 3.02/1.00  --res_to_prop_solver                    active
% 3.02/1.00  --res_prop_simpl_new                    false
% 3.02/1.00  --res_prop_simpl_given                  true
% 3.02/1.00  --res_passive_queue_type                priority_queues
% 3.02/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/1.00  --res_passive_queues_freq               [15;5]
% 3.02/1.00  --res_forward_subs                      full
% 3.02/1.00  --res_backward_subs                     full
% 3.02/1.00  --res_forward_subs_resolution           true
% 3.02/1.00  --res_backward_subs_resolution          true
% 3.02/1.00  --res_orphan_elimination                true
% 3.02/1.00  --res_time_limit                        2.
% 3.02/1.00  --res_out_proof                         true
% 3.02/1.00  
% 3.02/1.00  ------ Superposition Options
% 3.02/1.00  
% 3.02/1.00  --superposition_flag                    true
% 3.02/1.00  --sup_passive_queue_type                priority_queues
% 3.02/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.02/1.00  --demod_completeness_check              fast
% 3.02/1.00  --demod_use_ground                      true
% 3.02/1.00  --sup_to_prop_solver                    passive
% 3.02/1.00  --sup_prop_simpl_new                    true
% 3.02/1.00  --sup_prop_simpl_given                  true
% 3.02/1.00  --sup_fun_splitting                     false
% 3.02/1.00  --sup_smt_interval                      50000
% 3.02/1.00  
% 3.02/1.00  ------ Superposition Simplification Setup
% 3.02/1.00  
% 3.02/1.00  --sup_indices_passive                   []
% 3.02/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.00  --sup_full_bw                           [BwDemod]
% 3.02/1.00  --sup_immed_triv                        [TrivRules]
% 3.02/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.00  --sup_immed_bw_main                     []
% 3.02/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.00  
% 3.02/1.00  ------ Combination Options
% 3.02/1.00  
% 3.02/1.00  --comb_res_mult                         3
% 3.02/1.00  --comb_sup_mult                         2
% 3.02/1.00  --comb_inst_mult                        10
% 3.02/1.00  
% 3.02/1.00  ------ Debug Options
% 3.02/1.00  
% 3.02/1.00  --dbg_backtrace                         false
% 3.02/1.00  --dbg_dump_prop_clauses                 false
% 3.02/1.00  --dbg_dump_prop_clauses_file            -
% 3.02/1.00  --dbg_out_stat                          false
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  ------ Proving...
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  % SZS status Theorem for theBenchmark.p
% 3.02/1.00  
% 3.02/1.00   Resolution empty clause
% 3.02/1.00  
% 3.02/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.02/1.00  
% 3.02/1.00  fof(f17,axiom,(
% 3.02/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f34,plain,(
% 3.02/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.00    inference(ennf_transformation,[],[f17])).
% 3.02/1.00  
% 3.02/1.00  fof(f35,plain,(
% 3.02/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.00    inference(flattening,[],[f34])).
% 3.02/1.00  
% 3.02/1.00  fof(f56,plain,(
% 3.02/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.00    inference(nnf_transformation,[],[f35])).
% 3.02/1.00  
% 3.02/1.00  fof(f86,plain,(
% 3.02/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/1.00    inference(cnf_transformation,[],[f56])).
% 3.02/1.00  
% 3.02/1.00  fof(f20,conjecture,(
% 3.02/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f21,negated_conjecture,(
% 3.02/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.02/1.00    inference(negated_conjecture,[],[f20])).
% 3.02/1.00  
% 3.02/1.00  fof(f40,plain,(
% 3.02/1.00    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.02/1.00    inference(ennf_transformation,[],[f21])).
% 3.02/1.00  
% 3.02/1.00  fof(f41,plain,(
% 3.02/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.02/1.00    inference(flattening,[],[f40])).
% 3.02/1.00  
% 3.02/1.00  fof(f57,plain,(
% 3.02/1.00    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))) & k2_relset_1(sK4,sK5,sK6) = sK5 & v2_funct_1(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 3.02/1.00    introduced(choice_axiom,[])).
% 3.02/1.00  
% 3.02/1.00  fof(f58,plain,(
% 3.02/1.00    (~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))) & k2_relset_1(sK4,sK5,sK6) = sK5 & v2_funct_1(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 3.02/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f41,f57])).
% 3.02/1.00  
% 3.02/1.00  fof(f99,plain,(
% 3.02/1.00    v1_funct_2(sK6,sK4,sK5)),
% 3.02/1.00    inference(cnf_transformation,[],[f58])).
% 3.02/1.00  
% 3.02/1.00  fof(f100,plain,(
% 3.02/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.02/1.00    inference(cnf_transformation,[],[f58])).
% 3.02/1.00  
% 3.02/1.00  fof(f14,axiom,(
% 3.02/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f32,plain,(
% 3.02/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.00    inference(ennf_transformation,[],[f14])).
% 3.02/1.00  
% 3.02/1.00  fof(f83,plain,(
% 3.02/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/1.00    inference(cnf_transformation,[],[f32])).
% 3.02/1.00  
% 3.02/1.00  fof(f13,axiom,(
% 3.02/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f31,plain,(
% 3.02/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.00    inference(ennf_transformation,[],[f13])).
% 3.02/1.00  
% 3.02/1.00  fof(f82,plain,(
% 3.02/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/1.00    inference(cnf_transformation,[],[f31])).
% 3.02/1.00  
% 3.02/1.00  fof(f11,axiom,(
% 3.02/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f29,plain,(
% 3.02/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.02/1.00    inference(ennf_transformation,[],[f11])).
% 3.02/1.00  
% 3.02/1.00  fof(f30,plain,(
% 3.02/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/1.00    inference(flattening,[],[f29])).
% 3.02/1.00  
% 3.02/1.00  fof(f79,plain,(
% 3.02/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f30])).
% 3.02/1.00  
% 3.02/1.00  fof(f101,plain,(
% 3.02/1.00    v2_funct_1(sK6)),
% 3.02/1.00    inference(cnf_transformation,[],[f58])).
% 3.02/1.00  
% 3.02/1.00  fof(f98,plain,(
% 3.02/1.00    v1_funct_1(sK6)),
% 3.02/1.00    inference(cnf_transformation,[],[f58])).
% 3.02/1.00  
% 3.02/1.00  fof(f18,axiom,(
% 3.02/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f36,plain,(
% 3.02/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.02/1.00    inference(ennf_transformation,[],[f18])).
% 3.02/1.00  
% 3.02/1.00  fof(f37,plain,(
% 3.02/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/1.00    inference(flattening,[],[f36])).
% 3.02/1.00  
% 3.02/1.00  fof(f94,plain,(
% 3.02/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f37])).
% 3.02/1.00  
% 3.02/1.00  fof(f15,axiom,(
% 3.02/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f33,plain,(
% 3.02/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.00    inference(ennf_transformation,[],[f15])).
% 3.02/1.00  
% 3.02/1.00  fof(f84,plain,(
% 3.02/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/1.00    inference(cnf_transformation,[],[f33])).
% 3.02/1.00  
% 3.02/1.00  fof(f102,plain,(
% 3.02/1.00    k2_relset_1(sK4,sK5,sK6) = sK5),
% 3.02/1.00    inference(cnf_transformation,[],[f58])).
% 3.02/1.00  
% 3.02/1.00  fof(f78,plain,(
% 3.02/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f30])).
% 3.02/1.00  
% 3.02/1.00  fof(f10,axiom,(
% 3.02/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f27,plain,(
% 3.02/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.02/1.00    inference(ennf_transformation,[],[f10])).
% 3.02/1.00  
% 3.02/1.00  fof(f28,plain,(
% 3.02/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/1.00    inference(flattening,[],[f27])).
% 3.02/1.00  
% 3.02/1.00  fof(f77,plain,(
% 3.02/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f28])).
% 3.02/1.00  
% 3.02/1.00  fof(f76,plain,(
% 3.02/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f28])).
% 3.02/1.00  
% 3.02/1.00  fof(f93,plain,(
% 3.02/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f37])).
% 3.02/1.00  
% 3.02/1.00  fof(f103,plain,(
% 3.02/1.00    ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))),
% 3.02/1.00    inference(cnf_transformation,[],[f58])).
% 3.02/1.00  
% 3.02/1.00  fof(f4,axiom,(
% 3.02/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f63,plain,(
% 3.02/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f4])).
% 3.02/1.00  
% 3.02/1.00  fof(f19,axiom,(
% 3.02/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f38,plain,(
% 3.02/1.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.02/1.00    inference(ennf_transformation,[],[f19])).
% 3.02/1.00  
% 3.02/1.00  fof(f39,plain,(
% 3.02/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.02/1.00    inference(flattening,[],[f38])).
% 3.02/1.00  
% 3.02/1.00  fof(f96,plain,(
% 3.02/1.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f39])).
% 3.02/1.00  
% 3.02/1.00  fof(f9,axiom,(
% 3.02/1.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f26,plain,(
% 3.02/1.00    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.02/1.00    inference(ennf_transformation,[],[f9])).
% 3.02/1.00  
% 3.02/1.00  fof(f54,plain,(
% 3.02/1.00    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.02/1.00    inference(nnf_transformation,[],[f26])).
% 3.02/1.00  
% 3.02/1.00  fof(f75,plain,(
% 3.02/1.00    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f54])).
% 3.02/1.00  
% 3.02/1.00  fof(f5,axiom,(
% 3.02/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f46,plain,(
% 3.02/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.02/1.00    inference(nnf_transformation,[],[f5])).
% 3.02/1.00  
% 3.02/1.00  fof(f47,plain,(
% 3.02/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.02/1.00    inference(flattening,[],[f46])).
% 3.02/1.00  
% 3.02/1.00  fof(f65,plain,(
% 3.02/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.02/1.00    inference(cnf_transformation,[],[f47])).
% 3.02/1.00  
% 3.02/1.00  fof(f105,plain,(
% 3.02/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.02/1.00    inference(equality_resolution,[],[f65])).
% 3.02/1.00  
% 3.02/1.00  cnf(c_32,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.02/1.00      | k1_xboole_0 = X2 ),
% 3.02/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_43,negated_conjecture,
% 3.02/1.00      ( v1_funct_2(sK6,sK4,sK5) ),
% 3.02/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_739,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.02/1.00      | sK4 != X1
% 3.02/1.00      | sK5 != X2
% 3.02/1.00      | sK6 != X0
% 3.02/1.00      | k1_xboole_0 = X2 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_32,c_43]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_740,plain,
% 3.02/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.02/1.00      | k1_relset_1(sK4,sK5,sK6) = sK4
% 3.02/1.00      | k1_xboole_0 = sK5 ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_739]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_42,negated_conjecture,
% 3.02/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.02/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_742,plain,
% 3.02/1.00      ( k1_relset_1(sK4,sK5,sK6) = sK4 | k1_xboole_0 = sK5 ),
% 3.02/1.00      inference(global_propositional_subsumption,[status(thm)],[c_740,c_42]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1539,plain,
% 3.02/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_24,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1543,plain,
% 3.02/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.02/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4171,plain,
% 3.02/1.00      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1539,c_1543]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4301,plain,
% 3.02/1.00      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_742,c_4171]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_23,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1544,plain,
% 3.02/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.02/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2725,plain,
% 3.02/1.00      ( v1_relat_1(sK6) = iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1539,c_1544]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_19,plain,
% 3.02/1.00      ( ~ v2_funct_1(X0)
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v1_relat_1(X0)
% 3.02/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_41,negated_conjecture,
% 3.02/1.00      ( v2_funct_1(sK6) ),
% 3.02/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_486,plain,
% 3.02/1.00      ( ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v1_relat_1(X0)
% 3.02/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.02/1.00      | sK6 != X0 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_41]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_487,plain,
% 3.02/1.00      ( ~ v1_funct_1(sK6)
% 3.02/1.00      | ~ v1_relat_1(sK6)
% 3.02/1.00      | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_486]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_44,negated_conjecture,
% 3.02/1.00      ( v1_funct_1(sK6) ),
% 3.02/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_489,plain,
% 3.02/1.00      ( ~ v1_relat_1(sK6) | k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 3.02/1.00      inference(global_propositional_subsumption,[status(thm)],[c_487,c_44]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1535,plain,
% 3.02/1.00      ( k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6)
% 3.02/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2799,plain,
% 3.02/1.00      ( k2_relat_1(k2_funct_1(sK6)) = k1_relat_1(sK6) ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_2725,c_1535]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_33,plain,
% 3.02/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v1_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1540,plain,
% 3.02/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.02/1.00      | v1_funct_1(X0) != iProver_top
% 3.02/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4583,plain,
% 3.02/1.00      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK6)),k1_relat_1(sK6)))) = iProver_top
% 3.02/1.00      | v1_funct_1(k2_funct_1(sK6)) != iProver_top
% 3.02/1.00      | v1_relat_1(k2_funct_1(sK6)) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_2799,c_1540]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_25,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1542,plain,
% 3.02/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.02/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3456,plain,
% 3.02/1.00      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1539,c_1542]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_40,negated_conjecture,
% 3.02/1.00      ( k2_relset_1(sK4,sK5,sK6) = sK5 ),
% 3.02/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3468,plain,
% 3.02/1.00      ( k2_relat_1(sK6) = sK5 ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_3456,c_40]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_20,plain,
% 3.02/1.00      ( ~ v2_funct_1(X0)
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v1_relat_1(X0)
% 3.02/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_472,plain,
% 3.02/1.00      ( ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v1_relat_1(X0)
% 3.02/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.02/1.00      | sK6 != X0 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_41]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_473,plain,
% 3.02/1.00      ( ~ v1_funct_1(sK6)
% 3.02/1.00      | ~ v1_relat_1(sK6)
% 3.02/1.00      | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_472]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_475,plain,
% 3.02/1.00      ( ~ v1_relat_1(sK6) | k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 3.02/1.00      inference(global_propositional_subsumption,[status(thm)],[c_473,c_44]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1536,plain,
% 3.02/1.00      ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6)
% 3.02/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_475]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2798,plain,
% 3.02/1.00      ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_2725,c_1536]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3539,plain,
% 3.02/1.00      ( k1_relat_1(k2_funct_1(sK6)) = sK5 ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_3468,c_2798]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4596,plain,
% 3.02/1.00      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK6)))) = iProver_top
% 3.02/1.00      | v1_funct_1(k2_funct_1(sK6)) != iProver_top
% 3.02/1.00      | v1_relat_1(k2_funct_1(sK6)) != iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_4583,c_3539]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_45,plain,
% 3.02/1.00      ( v1_funct_1(sK6) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_47,plain,
% 3.02/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_17,plain,
% 3.02/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1898,plain,
% 3.02/1.00      ( v1_funct_1(k2_funct_1(sK6)) | ~ v1_funct_1(sK6) | ~ v1_relat_1(sK6) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1899,plain,
% 3.02/1.00      ( v1_funct_1(k2_funct_1(sK6)) = iProver_top
% 3.02/1.00      | v1_funct_1(sK6) != iProver_top
% 3.02/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_1898]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1907,plain,
% 3.02/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK6) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2052,plain,
% 3.02/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.02/1.00      | v1_relat_1(sK6) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_1907]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2053,plain,
% 3.02/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.02/1.00      | v1_relat_1(sK6) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_2052]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_18,plain,
% 3.02/1.00      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.02/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4992,plain,
% 3.02/1.00      ( ~ v1_funct_1(sK6) | v1_relat_1(k2_funct_1(sK6)) | ~ v1_relat_1(sK6) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4993,plain,
% 3.02/1.00      ( v1_funct_1(sK6) != iProver_top
% 3.02/1.00      | v1_relat_1(k2_funct_1(sK6)) = iProver_top
% 3.02/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_4992]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5075,plain,
% 3.02/1.00      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK6)))) = iProver_top ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_4596,c_45,c_47,c_1899,c_2053,c_4993]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5083,plain,
% 3.02/1.00      ( k1_relset_1(sK5,k1_relat_1(sK6),k2_funct_1(sK6)) = k1_relat_1(k2_funct_1(sK6)) ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_5075,c_1543]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5089,plain,
% 3.02/1.00      ( k1_relset_1(sK5,k1_relat_1(sK6),k2_funct_1(sK6)) = sK5 ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_5083,c_3539]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5105,plain,
% 3.02/1.00      ( k1_relset_1(sK5,sK4,k2_funct_1(sK6)) = sK5 | sK5 = k1_xboole_0 ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_4301,c_5089]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_34,plain,
% 3.02/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v1_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_39,negated_conjecture,
% 3.02/1.00      ( ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
% 3.02/1.00      | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 3.02/1.00      | ~ v1_funct_1(k2_funct_1(sK6)) ),
% 3.02/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_750,plain,
% 3.02/1.00      ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v1_funct_1(k2_funct_1(sK6))
% 3.02/1.00      | ~ v1_relat_1(X0)
% 3.02/1.00      | k2_funct_1(sK6) != X0
% 3.02/1.00      | k1_relat_1(X0) != sK5
% 3.02/1.00      | k2_relat_1(X0) != sK4 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_34,c_39]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_751,plain,
% 3.02/1.00      ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 3.02/1.00      | ~ v1_funct_1(k2_funct_1(sK6))
% 3.02/1.00      | ~ v1_relat_1(k2_funct_1(sK6))
% 3.02/1.00      | k1_relat_1(k2_funct_1(sK6)) != sK5
% 3.02/1.00      | k2_relat_1(k2_funct_1(sK6)) != sK4 ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_750]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_763,plain,
% 3.02/1.00      ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 3.02/1.00      | ~ v1_funct_1(k2_funct_1(sK6))
% 3.02/1.00      | k1_relat_1(k2_funct_1(sK6)) != sK5
% 3.02/1.00      | k2_relat_1(k2_funct_1(sK6)) != sK4 ),
% 3.02/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_751,c_23]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1524,plain,
% 3.02/1.00      ( k1_relat_1(k2_funct_1(sK6)) != sK5
% 3.02/1.00      | k2_relat_1(k2_funct_1(sK6)) != sK4
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 3.02/1.00      | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_763]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_768,plain,
% 3.02/1.00      ( k1_relat_1(k2_funct_1(sK6)) != sK5
% 3.02/1.00      | k2_relat_1(k2_funct_1(sK6)) != sK4
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 3.02/1.00      | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_763]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2162,plain,
% 3.02/1.00      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 3.02/1.00      | k2_relat_1(k2_funct_1(sK6)) != sK4
% 3.02/1.00      | k1_relat_1(k2_funct_1(sK6)) != sK5 ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_1524,c_45,c_47,c_768,c_1899,c_2053]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2163,plain,
% 3.02/1.00      ( k1_relat_1(k2_funct_1(sK6)) != sK5
% 3.02/1.00      | k2_relat_1(k2_funct_1(sK6)) != sK4
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_2162]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2805,plain,
% 3.02/1.00      ( k2_relat_1(k2_funct_1(sK6)) != sK4
% 3.02/1.00      | k2_relat_1(sK6) != sK5
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_2798,c_2163]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2867,plain,
% 3.02/1.00      ( k1_relat_1(sK6) != sK4
% 3.02/1.00      | k2_relat_1(sK6) != sK5
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_2805,c_2799]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3538,plain,
% 3.02/1.00      ( k1_relat_1(sK6) != sK4
% 3.02/1.00      | sK5 != sK5
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_3468,c_2867]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3542,plain,
% 3.02/1.00      ( k1_relat_1(sK6) != sK4
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
% 3.02/1.00      inference(equality_resolution_simp,[status(thm)],[c_3538]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4350,plain,
% 3.02/1.00      ( sK5 = k1_xboole_0
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_4301,c_3542]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4,plain,
% 3.02/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_37,plain,
% 3.02/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.02/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v1_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_426,plain,
% 3.02/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v1_relat_1(X0)
% 3.02/1.00      | X1 != X2
% 3.02/1.00      | k2_relat_1(X0) != k1_xboole_0 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_37]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_427,plain,
% 3.02/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v1_relat_1(X0)
% 3.02/1.00      | k2_relat_1(X0) != k1_xboole_0 ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_426]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_769,plain,
% 3.02/1.00      ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v1_funct_1(k2_funct_1(sK6))
% 3.02/1.00      | ~ v1_relat_1(X0)
% 3.02/1.00      | k2_funct_1(sK6) != X0
% 3.02/1.00      | k1_relat_1(X0) != sK5
% 3.02/1.00      | k2_relat_1(X0) != k1_xboole_0
% 3.02/1.00      | sK4 != X1 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_427,c_39]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_770,plain,
% 3.02/1.00      ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 3.02/1.00      | ~ v1_funct_1(k2_funct_1(sK6))
% 3.02/1.00      | ~ v1_relat_1(k2_funct_1(sK6))
% 3.02/1.00      | k1_relat_1(k2_funct_1(sK6)) != sK5
% 3.02/1.00      | k2_relat_1(k2_funct_1(sK6)) != k1_xboole_0 ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_769]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_782,plain,
% 3.02/1.00      ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 3.02/1.00      | ~ v1_funct_1(k2_funct_1(sK6))
% 3.02/1.00      | k1_relat_1(k2_funct_1(sK6)) != sK5
% 3.02/1.00      | k2_relat_1(k2_funct_1(sK6)) != k1_xboole_0 ),
% 3.02/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_770,c_23]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1523,plain,
% 3.02/1.00      ( k1_relat_1(k2_funct_1(sK6)) != sK5
% 3.02/1.00      | k2_relat_1(k2_funct_1(sK6)) != k1_xboole_0
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 3.02/1.00      | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_782]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2806,plain,
% 3.02/1.00      ( k2_relat_1(k2_funct_1(sK6)) != k1_xboole_0
% 3.02/1.00      | k2_relat_1(sK6) != sK5
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 3.02/1.00      | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_2798,c_1523]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3225,plain,
% 3.02/1.00      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 3.02/1.00      | k2_relat_1(sK6) != sK5
% 3.02/1.00      | k2_relat_1(k2_funct_1(sK6)) != k1_xboole_0 ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_2806,c_45,c_47,c_1899,c_2053]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3226,plain,
% 3.02/1.00      ( k2_relat_1(k2_funct_1(sK6)) != k1_xboole_0
% 3.02/1.00      | k2_relat_1(sK6) != sK5
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_3225]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3229,plain,
% 3.02/1.00      ( k1_relat_1(sK6) != k1_xboole_0
% 3.02/1.00      | k2_relat_1(sK6) != sK5
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_3226,c_2799]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_15,plain,
% 3.02/1.00      ( ~ v1_relat_1(X0)
% 3.02/1.00      | k1_relat_1(X0) = k1_xboole_0
% 3.02/1.00      | k2_relat_1(X0) != k1_xboole_0 ),
% 3.02/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1550,plain,
% 3.02/1.00      ( k1_relat_1(X0) = k1_xboole_0
% 3.02/1.00      | k2_relat_1(X0) != k1_xboole_0
% 3.02/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3572,plain,
% 3.02/1.00      ( k1_relat_1(sK6) = k1_xboole_0
% 3.02/1.00      | sK5 != k1_xboole_0
% 3.02/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_3468,c_1550]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3808,plain,
% 3.02/1.00      ( sK5 != k1_xboole_0 | k1_relat_1(sK6) = k1_xboole_0 ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_3572,c_47,c_2053]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3809,plain,
% 3.02/1.00      ( k1_relat_1(sK6) = k1_xboole_0 | sK5 != k1_xboole_0 ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_3808]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4451,plain,
% 3.02/1.00      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_4350,c_3229,c_3468,c_3809]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5080,plain,
% 3.02/1.00      ( sK5 = k1_xboole_0
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_4301,c_5075]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5128,plain,
% 3.02/1.00      ( sK5 = k1_xboole_0 ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_5105,c_3229,c_3468,c_3809,c_4350,c_5080]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5132,plain,
% 3.02/1.00      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK6)))) = iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_5128,c_5075]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5147,plain,
% 3.02/1.00      ( k1_relat_1(sK6) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_5128,c_3809]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5209,plain,
% 3.02/1.00      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 3.02/1.00      inference(equality_resolution_simp,[status(thm)],[c_5147]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5265,plain,
% 3.02/1.00      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_5132,c_5209]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_6,plain,
% 3.02/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.02/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5267,plain,
% 3.02/1.00      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_5265,c_6]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3535,plain,
% 3.02/1.00      ( k1_relat_1(sK6) != k1_xboole_0
% 3.02/1.00      | sK5 != sK5
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_3468,c_3229]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3555,plain,
% 3.02/1.00      ( k1_relat_1(sK6) != k1_xboole_0
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
% 3.02/1.00      inference(equality_resolution_simp,[status(thm)],[c_3535]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5143,plain,
% 3.02/1.00      ( k1_relat_1(sK6) != k1_xboole_0
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_5128,c_3555]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5231,plain,
% 3.02/1.00      ( k1_xboole_0 != k1_xboole_0
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_5143,c_5209]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5232,plain,
% 3.02/1.00      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top ),
% 3.02/1.00      inference(equality_resolution_simp,[status(thm)],[c_5231]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5234,plain,
% 3.02/1.00      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_5232,c_6]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5269,plain,
% 3.02/1.00      ( $false ),
% 3.02/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_5267,c_5234]) ).
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.02/1.00  
% 3.02/1.00  ------                               Statistics
% 3.02/1.00  
% 3.02/1.00  ------ General
% 3.02/1.00  
% 3.02/1.00  abstr_ref_over_cycles:                  0
% 3.02/1.00  abstr_ref_under_cycles:                 0
% 3.02/1.00  gc_basic_clause_elim:                   0
% 3.02/1.00  forced_gc_time:                         0
% 3.02/1.00  parsing_time:                           0.012
% 3.02/1.00  unif_index_cands_time:                  0.
% 3.02/1.00  unif_index_add_time:                    0.
% 3.02/1.00  orderings_time:                         0.
% 3.02/1.00  out_proof_time:                         0.01
% 3.02/1.00  total_time:                             0.181
% 3.02/1.00  num_of_symbols:                         56
% 3.02/1.00  num_of_terms:                           5116
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing
% 3.02/1.00  
% 3.02/1.00  num_of_splits:                          0
% 3.02/1.00  num_of_split_atoms:                     0
% 3.02/1.00  num_of_reused_defs:                     0
% 3.02/1.00  num_eq_ax_congr_red:                    19
% 3.02/1.00  num_of_sem_filtered_clauses:            1
% 3.02/1.00  num_of_subtypes:                        0
% 3.02/1.00  monotx_restored_types:                  0
% 3.02/1.00  sat_num_of_epr_types:                   0
% 3.02/1.00  sat_num_of_non_cyclic_types:            0
% 3.02/1.00  sat_guarded_non_collapsed_types:        0
% 3.02/1.00  num_pure_diseq_elim:                    0
% 3.02/1.00  simp_replaced_by:                       0
% 3.02/1.00  res_preprocessed:                       164
% 3.02/1.00  prep_upred:                             0
% 3.02/1.00  prep_unflattend:                        55
% 3.02/1.00  smt_new_axioms:                         0
% 3.02/1.00  pred_elim_cands:                        8
% 3.02/1.00  pred_elim:                              3
% 3.02/1.00  pred_elim_cl:                           -2
% 3.02/1.00  pred_elim_cycles:                       4
% 3.02/1.00  merged_defs:                            0
% 3.02/1.00  merged_defs_ncl:                        0
% 3.02/1.00  bin_hyper_res:                          0
% 3.02/1.00  prep_cycles:                            3
% 3.02/1.00  pred_elim_time:                         0.011
% 3.02/1.00  splitting_time:                         0.
% 3.02/1.00  sem_filter_time:                        0.
% 3.02/1.00  monotx_time:                            0.001
% 3.02/1.00  subtype_inf_time:                       0.
% 3.02/1.00  
% 3.02/1.00  ------ Problem properties
% 3.02/1.00  
% 3.02/1.00  clauses:                                45
% 3.02/1.00  conjectures:                            3
% 3.02/1.00  epr:                                    6
% 3.02/1.00  horn:                                   37
% 3.02/1.00  ground:                                 19
% 3.02/1.00  unary:                                  11
% 3.02/1.00  binary:                                 11
% 3.02/1.00  lits:                                   120
% 3.02/1.00  lits_eq:                                52
% 3.02/1.00  fd_pure:                                0
% 3.02/1.00  fd_pseudo:                              0
% 3.02/1.00  fd_cond:                                4
% 3.02/1.00  fd_pseudo_cond:                         2
% 3.02/1.00  ac_symbols:                             0
% 3.02/1.00  
% 3.02/1.00  ------ Propositional Solver
% 3.02/1.00  
% 3.02/1.00  prop_solver_calls:                      24
% 3.02/1.00  prop_fast_solver_calls:                 1203
% 3.02/1.00  smt_solver_calls:                       0
% 3.02/1.00  smt_fast_solver_calls:                  0
% 3.02/1.00  prop_num_of_clauses:                    1876
% 3.02/1.00  prop_preprocess_simplified:             6090
% 3.02/1.00  prop_fo_subsumed:                       31
% 3.02/1.00  prop_solver_time:                       0.
% 3.02/1.00  smt_solver_time:                        0.
% 3.02/1.00  smt_fast_solver_time:                   0.
% 3.02/1.00  prop_fast_solver_time:                  0.
% 3.02/1.00  prop_unsat_core_time:                   0.
% 3.02/1.00  
% 3.02/1.00  ------ QBF
% 3.02/1.00  
% 3.02/1.00  qbf_q_res:                              0
% 3.02/1.00  qbf_num_tautologies:                    0
% 3.02/1.00  qbf_prep_cycles:                        0
% 3.02/1.00  
% 3.02/1.00  ------ BMC1
% 3.02/1.00  
% 3.02/1.00  bmc1_current_bound:                     -1
% 3.02/1.00  bmc1_last_solved_bound:                 -1
% 3.02/1.00  bmc1_unsat_core_size:                   -1
% 3.02/1.00  bmc1_unsat_core_parents_size:           -1
% 3.02/1.00  bmc1_merge_next_fun:                    0
% 3.02/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.02/1.00  
% 3.02/1.00  ------ Instantiation
% 3.02/1.00  
% 3.02/1.00  inst_num_of_clauses:                    663
% 3.02/1.00  inst_num_in_passive:                    209
% 3.02/1.00  inst_num_in_active:                     299
% 3.02/1.00  inst_num_in_unprocessed:                155
% 3.02/1.00  inst_num_of_loops:                      400
% 3.02/1.00  inst_num_of_learning_restarts:          0
% 3.02/1.00  inst_num_moves_active_passive:          98
% 3.02/1.00  inst_lit_activity:                      0
% 3.02/1.00  inst_lit_activity_moves:                0
% 3.02/1.00  inst_num_tautologies:                   0
% 3.02/1.00  inst_num_prop_implied:                  0
% 3.02/1.00  inst_num_existing_simplified:           0
% 3.02/1.00  inst_num_eq_res_simplified:             0
% 3.02/1.00  inst_num_child_elim:                    0
% 3.02/1.00  inst_num_of_dismatching_blockings:      156
% 3.02/1.00  inst_num_of_non_proper_insts:           373
% 3.02/1.00  inst_num_of_duplicates:                 0
% 3.02/1.00  inst_inst_num_from_inst_to_res:         0
% 3.02/1.00  inst_dismatching_checking_time:         0.
% 3.02/1.00  
% 3.02/1.00  ------ Resolution
% 3.02/1.00  
% 3.02/1.00  res_num_of_clauses:                     0
% 3.02/1.00  res_num_in_passive:                     0
% 3.02/1.00  res_num_in_active:                      0
% 3.02/1.00  res_num_of_loops:                       167
% 3.02/1.00  res_forward_subset_subsumed:            13
% 3.02/1.00  res_backward_subset_subsumed:           2
% 3.02/1.00  res_forward_subsumed:                   0
% 3.02/1.00  res_backward_subsumed:                  0
% 3.02/1.00  res_forward_subsumption_resolution:     5
% 3.02/1.00  res_backward_subsumption_resolution:    0
% 3.02/1.00  res_clause_to_clause_subsumption:       192
% 3.02/1.00  res_orphan_elimination:                 0
% 3.02/1.00  res_tautology_del:                      68
% 3.02/1.00  res_num_eq_res_simplified:              0
% 3.02/1.00  res_num_sel_changes:                    0
% 3.02/1.00  res_moves_from_active_to_pass:          0
% 3.02/1.00  
% 3.02/1.00  ------ Superposition
% 3.02/1.00  
% 3.02/1.00  sup_time_total:                         0.
% 3.02/1.00  sup_time_generating:                    0.
% 3.02/1.00  sup_time_sim_full:                      0.
% 3.02/1.00  sup_time_sim_immed:                     0.
% 3.02/1.00  
% 3.02/1.00  sup_num_of_clauses:                     66
% 3.02/1.00  sup_num_in_active:                      39
% 3.02/1.00  sup_num_in_passive:                     27
% 3.02/1.00  sup_num_of_loops:                       78
% 3.02/1.00  sup_fw_superposition:                   52
% 3.02/1.00  sup_bw_superposition:                   28
% 3.02/1.00  sup_immediate_simplified:               28
% 3.02/1.00  sup_given_eliminated:                   0
% 3.02/1.00  comparisons_done:                       0
% 3.02/1.00  comparisons_avoided:                    5
% 3.02/1.00  
% 3.02/1.00  ------ Simplifications
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  sim_fw_subset_subsumed:                 8
% 3.02/1.00  sim_bw_subset_subsumed:                 6
% 3.02/1.00  sim_fw_subsumed:                        2
% 3.02/1.00  sim_bw_subsumed:                        6
% 3.02/1.00  sim_fw_subsumption_res:                 2
% 3.02/1.00  sim_bw_subsumption_res:                 1
% 3.02/1.00  sim_tautology_del:                      3
% 3.02/1.00  sim_eq_tautology_del:                   7
% 3.02/1.00  sim_eq_res_simp:                        10
% 3.02/1.00  sim_fw_demodulated:                     23
% 3.02/1.00  sim_bw_demodulated:                     38
% 3.02/1.00  sim_light_normalised:                   30
% 3.02/1.00  sim_joinable_taut:                      0
% 3.02/1.00  sim_joinable_simp:                      0
% 3.02/1.00  sim_ac_normalised:                      0
% 3.02/1.00  sim_smt_subsumption:                    0
% 3.02/1.00  
%------------------------------------------------------------------------------
