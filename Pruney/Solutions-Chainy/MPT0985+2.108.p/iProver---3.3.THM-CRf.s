%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:42 EST 2020

% Result     : Theorem 6.02s
% Output     : CNFRefutation 6.02s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 768 expanded)
%              Number of clauses        :   85 ( 257 expanded)
%              Number of leaves         :   14 ( 148 expanded)
%              Depth                    :   20
%              Number of atoms          :  425 (3847 expanded)
%              Number of equality atoms :  172 ( 713 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,conjecture,(
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

fof(f45,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f44])).

fof(f83,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f84,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f83])).

fof(f98,plain,
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

fof(f99,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
      | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
      | ~ v1_funct_1(k2_funct_1(sK6)) )
    & k2_relset_1(sK4,sK5,sK6) = sK5
    & v2_funct_1(sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f84,f98])).

fof(f178,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f99])).

fof(f37,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f145,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f180,plain,(
    k2_relset_1(sK4,sK5,sK6) = sK5 ),
    inference(cnf_transformation,[],[f99])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f60])).

fof(f136,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f122,plain,(
    ! [X0] :
      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f43,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f81])).

fof(f175,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f123,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f176,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f99])).

fof(f179,plain,(
    v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f99])).

fof(f26,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f131,plain,(
    ! [X0] :
      ( v1_funct_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f130,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f118,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f64])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f25,axiom,(
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
    inference(ennf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f129,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f181,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
    | ~ v1_funct_1(k2_funct_1(sK6)) ),
    inference(cnf_transformation,[],[f99])).

fof(f27,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f56])).

fof(f133,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f174,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_69,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f178])).

cnf(c_10896,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_10927,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_17063,plain,
    ( k7_relset_1(sK4,sK5,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_10896,c_10927])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_10925,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_18183,plain,
    ( k7_relset_1(sK4,sK5,sK6,sK4) = k2_relset_1(sK4,sK5,sK6) ),
    inference(superposition,[status(thm)],[c_10896,c_10925])).

cnf(c_67,negated_conjecture,
    ( k2_relset_1(sK4,sK5,sK6) = sK5 ),
    inference(cnf_transformation,[],[f180])).

cnf(c_18215,plain,
    ( k7_relset_1(sK4,sK5,sK6,sK4) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_18183,c_67])).

cnf(c_18250,plain,
    ( k9_relat_1(sK6,sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_17063,c_18215])).

cnf(c_26,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_10936,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24999,plain,
    ( r1_tarski(k10_relat_1(sK6,sK5),sK4) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v2_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_18250,c_10936])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_10928,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_14536,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_10896,c_10928])).

cnf(c_14576,plain,
    ( k2_relat_1(sK6) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_14536,c_67])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_10930,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_11954,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_10896,c_10930])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_10948,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12107,plain,
    ( k1_relat_1(k4_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_11954,c_10948])).

cnf(c_63,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f175])).

cnf(c_10900,plain,
    ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_12126,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(sK6)),X0) != iProver_top
    | m1_subset_1(k4_relat_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK6),X0))) = iProver_top
    | v1_funct_1(k4_relat_1(sK6)) != iProver_top
    | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12107,c_10900])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_10949,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_12106,plain,
    ( k2_relat_1(k4_relat_1(sK6)) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_11954,c_10949])).

cnf(c_12141,plain,
    ( r1_tarski(k1_relat_1(sK6),X0) != iProver_top
    | m1_subset_1(k4_relat_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK6),X0))) = iProver_top
    | v1_funct_1(k4_relat_1(sK6)) != iProver_top
    | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12126,c_12106])).

cnf(c_71,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f176])).

cnf(c_72,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_74,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_68,negated_conjecture,
    ( v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f179])).

cnf(c_75,plain,
    ( v2_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k4_relat_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_11497,plain,
    ( v1_funct_1(k4_relat_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v2_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_11498,plain,
    ( v1_funct_1(k4_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v2_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11497])).

cnf(c_21,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_11500,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v2_funct_1(sK6)
    | v1_relat_1(k4_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_11501,plain,
    ( v1_funct_1(sK6) != iProver_top
    | v2_funct_1(sK6) != iProver_top
    | v1_relat_1(k4_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11500])).

cnf(c_11514,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_11515,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11514])).

cnf(c_12165,plain,
    ( r1_tarski(k1_relat_1(sK6),X0) != iProver_top
    | m1_subset_1(k4_relat_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK6),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12141,c_72,c_74,c_75,c_11498,c_11501,c_11515])).

cnf(c_12174,plain,
    ( r1_tarski(k1_relat_1(sK6),X0) != iProver_top
    | v1_relat_1(k4_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12165,c_10930])).

cnf(c_12286,plain,
    ( v1_relat_1(k4_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12174,c_72,c_74,c_75,c_11501,c_11515])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_10951,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12291,plain,
    ( k9_relat_1(k4_relat_1(sK6),k1_relat_1(k4_relat_1(sK6))) = k2_relat_1(k4_relat_1(sK6)) ),
    inference(superposition,[status(thm)],[c_12286,c_10951])).

cnf(c_12301,plain,
    ( k9_relat_1(k4_relat_1(sK6),k2_relat_1(sK6)) = k1_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_12291,c_12106,c_12107])).

cnf(c_14687,plain,
    ( k9_relat_1(k4_relat_1(sK6),sK5) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_14576,c_12301])).

cnf(c_10894,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_28,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_10934,plain,
    ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23928,plain,
    ( k9_relat_1(k2_funct_1(sK6),X0) = k10_relat_1(sK6,X0)
    | v2_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_10894,c_10934])).

cnf(c_11580,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v2_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k9_relat_1(k2_funct_1(sK6),X0) = k10_relat_1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_24296,plain,
    ( k9_relat_1(k2_funct_1(sK6),X0) = k10_relat_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23928,c_71,c_69,c_68,c_11514,c_11580])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_10943,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_23991,plain,
    ( k2_funct_1(sK6) = k4_relat_1(sK6)
    | v2_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_10894,c_10943])).

cnf(c_11544,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v2_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k2_funct_1(sK6) = k4_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_24247,plain,
    ( k2_funct_1(sK6) = k4_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23991,c_71,c_69,c_68,c_11514,c_11544])).

cnf(c_24299,plain,
    ( k9_relat_1(k4_relat_1(sK6),X0) = k10_relat_1(sK6,X0) ),
    inference(light_normalisation,[status(thm)],[c_24296,c_24247])).

cnf(c_24314,plain,
    ( k10_relat_1(sK6,sK5) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_14687,c_24299])).

cnf(c_25004,plain,
    ( r1_tarski(k1_relat_1(sK6),sK4) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v2_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24999,c_24314])).

cnf(c_14689,plain,
    ( r1_tarski(k1_relat_1(sK6),X0) != iProver_top
    | m1_subset_1(k4_relat_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14576,c_12165])).

cnf(c_66,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
    | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(k2_funct_1(sK6)) ),
    inference(cnf_transformation,[],[f181])).

cnf(c_10898,plain,
    ( v1_funct_2(k2_funct_1(sK6),sK5,sK4) != iProver_top
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_76,plain,
    ( v1_funct_2(k2_funct_1(sK6),sK5,sK4) != iProver_top
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_23,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_11517,plain,
    ( v1_funct_1(k2_funct_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v2_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_11518,plain,
    ( v1_funct_1(k2_funct_1(sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v2_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11517])).

cnf(c_11526,plain,
    ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | v1_funct_2(k2_funct_1(sK6),sK5,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10898,c_72,c_74,c_75,c_76,c_11515,c_11518])).

cnf(c_11527,plain,
    ( v1_funct_2(k2_funct_1(sK6),sK5,sK4) != iProver_top
    | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11526])).

cnf(c_24260,plain,
    ( v1_funct_2(k4_relat_1(sK6),sK5,sK4) != iProver_top
    | m1_subset_1(k4_relat_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24247,c_11527])).

cnf(c_24287,plain,
    ( v1_funct_2(k4_relat_1(sK6),sK5,sK4) != iProver_top
    | r1_tarski(k1_relat_1(sK6),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_14689,c_24260])).

cnf(c_64,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f174])).

cnf(c_10899,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_12127,plain,
    ( v1_funct_2(k4_relat_1(sK6),k2_relat_1(sK6),X0) = iProver_top
    | r1_tarski(k2_relat_1(k4_relat_1(sK6)),X0) != iProver_top
    | v1_funct_1(k4_relat_1(sK6)) != iProver_top
    | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12107,c_10899])).

cnf(c_12132,plain,
    ( v1_funct_2(k4_relat_1(sK6),k2_relat_1(sK6),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK6),X0) != iProver_top
    | v1_funct_1(k4_relat_1(sK6)) != iProver_top
    | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12127,c_12106])).

cnf(c_12156,plain,
    ( v1_funct_2(k4_relat_1(sK6),k2_relat_1(sK6),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12132,c_72,c_74,c_75,c_11498,c_11501,c_11515])).

cnf(c_14690,plain,
    ( v1_funct_2(k4_relat_1(sK6),sK5,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14576,c_12156])).

cnf(c_24462,plain,
    ( r1_tarski(k1_relat_1(sK6),sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_24287,c_14690])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25004,c_24462,c_11515,c_75,c_74,c_72])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:20:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 6.02/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.02/1.49  
% 6.02/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.02/1.49  
% 6.02/1.49  ------  iProver source info
% 6.02/1.49  
% 6.02/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.02/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.02/1.49  git: non_committed_changes: false
% 6.02/1.49  git: last_make_outside_of_git: false
% 6.02/1.49  
% 6.02/1.49  ------ 
% 6.02/1.49  
% 6.02/1.49  ------ Input Options
% 6.02/1.49  
% 6.02/1.49  --out_options                           all
% 6.02/1.49  --tptp_safe_out                         true
% 6.02/1.49  --problem_path                          ""
% 6.02/1.49  --include_path                          ""
% 6.02/1.49  --clausifier                            res/vclausify_rel
% 6.02/1.49  --clausifier_options                    --mode clausify
% 6.02/1.49  --stdin                                 false
% 6.02/1.49  --stats_out                             all
% 6.02/1.49  
% 6.02/1.49  ------ General Options
% 6.02/1.49  
% 6.02/1.49  --fof                                   false
% 6.02/1.49  --time_out_real                         305.
% 6.02/1.49  --time_out_virtual                      -1.
% 6.02/1.49  --symbol_type_check                     false
% 6.02/1.49  --clausify_out                          false
% 6.02/1.49  --sig_cnt_out                           false
% 6.02/1.49  --trig_cnt_out                          false
% 6.02/1.49  --trig_cnt_out_tolerance                1.
% 6.02/1.49  --trig_cnt_out_sk_spl                   false
% 6.02/1.49  --abstr_cl_out                          false
% 6.02/1.49  
% 6.02/1.49  ------ Global Options
% 6.02/1.49  
% 6.02/1.49  --schedule                              default
% 6.02/1.49  --add_important_lit                     false
% 6.02/1.49  --prop_solver_per_cl                    1000
% 6.02/1.49  --min_unsat_core                        false
% 6.02/1.49  --soft_assumptions                      false
% 6.02/1.49  --soft_lemma_size                       3
% 6.02/1.49  --prop_impl_unit_size                   0
% 6.02/1.49  --prop_impl_unit                        []
% 6.02/1.49  --share_sel_clauses                     true
% 6.02/1.49  --reset_solvers                         false
% 6.02/1.49  --bc_imp_inh                            [conj_cone]
% 6.02/1.49  --conj_cone_tolerance                   3.
% 6.02/1.49  --extra_neg_conj                        none
% 6.02/1.49  --large_theory_mode                     true
% 6.02/1.49  --prolific_symb_bound                   200
% 6.02/1.49  --lt_threshold                          2000
% 6.02/1.49  --clause_weak_htbl                      true
% 6.02/1.49  --gc_record_bc_elim                     false
% 6.02/1.50  
% 6.02/1.50  ------ Preprocessing Options
% 6.02/1.50  
% 6.02/1.50  --preprocessing_flag                    true
% 6.02/1.50  --time_out_prep_mult                    0.1
% 6.02/1.50  --splitting_mode                        input
% 6.02/1.50  --splitting_grd                         true
% 6.02/1.50  --splitting_cvd                         false
% 6.02/1.50  --splitting_cvd_svl                     false
% 6.02/1.50  --splitting_nvd                         32
% 6.02/1.50  --sub_typing                            true
% 6.02/1.50  --prep_gs_sim                           true
% 6.02/1.50  --prep_unflatten                        true
% 6.02/1.50  --prep_res_sim                          true
% 6.02/1.50  --prep_upred                            true
% 6.02/1.50  --prep_sem_filter                       exhaustive
% 6.02/1.50  --prep_sem_filter_out                   false
% 6.02/1.50  --pred_elim                             true
% 6.02/1.50  --res_sim_input                         true
% 6.02/1.50  --eq_ax_congr_red                       true
% 6.02/1.50  --pure_diseq_elim                       true
% 6.02/1.50  --brand_transform                       false
% 6.02/1.50  --non_eq_to_eq                          false
% 6.02/1.50  --prep_def_merge                        true
% 6.02/1.50  --prep_def_merge_prop_impl              false
% 6.02/1.50  --prep_def_merge_mbd                    true
% 6.02/1.50  --prep_def_merge_tr_red                 false
% 6.02/1.50  --prep_def_merge_tr_cl                  false
% 6.02/1.50  --smt_preprocessing                     true
% 6.02/1.50  --smt_ac_axioms                         fast
% 6.02/1.50  --preprocessed_out                      false
% 6.02/1.50  --preprocessed_stats                    false
% 6.02/1.50  
% 6.02/1.50  ------ Abstraction refinement Options
% 6.02/1.50  
% 6.02/1.50  --abstr_ref                             []
% 6.02/1.50  --abstr_ref_prep                        false
% 6.02/1.50  --abstr_ref_until_sat                   false
% 6.02/1.50  --abstr_ref_sig_restrict                funpre
% 6.02/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.02/1.50  --abstr_ref_under                       []
% 6.02/1.50  
% 6.02/1.50  ------ SAT Options
% 6.02/1.50  
% 6.02/1.50  --sat_mode                              false
% 6.02/1.50  --sat_fm_restart_options                ""
% 6.02/1.50  --sat_gr_def                            false
% 6.02/1.50  --sat_epr_types                         true
% 6.02/1.50  --sat_non_cyclic_types                  false
% 6.02/1.50  --sat_finite_models                     false
% 6.02/1.50  --sat_fm_lemmas                         false
% 6.02/1.50  --sat_fm_prep                           false
% 6.02/1.50  --sat_fm_uc_incr                        true
% 6.02/1.50  --sat_out_model                         small
% 6.02/1.50  --sat_out_clauses                       false
% 6.02/1.50  
% 6.02/1.50  ------ QBF Options
% 6.02/1.50  
% 6.02/1.50  --qbf_mode                              false
% 6.02/1.50  --qbf_elim_univ                         false
% 6.02/1.50  --qbf_dom_inst                          none
% 6.02/1.50  --qbf_dom_pre_inst                      false
% 6.02/1.50  --qbf_sk_in                             false
% 6.02/1.50  --qbf_pred_elim                         true
% 6.02/1.50  --qbf_split                             512
% 6.02/1.50  
% 6.02/1.50  ------ BMC1 Options
% 6.02/1.50  
% 6.02/1.50  --bmc1_incremental                      false
% 6.02/1.50  --bmc1_axioms                           reachable_all
% 6.02/1.50  --bmc1_min_bound                        0
% 6.02/1.50  --bmc1_max_bound                        -1
% 6.02/1.50  --bmc1_max_bound_default                -1
% 6.02/1.50  --bmc1_symbol_reachability              true
% 6.02/1.50  --bmc1_property_lemmas                  false
% 6.02/1.50  --bmc1_k_induction                      false
% 6.02/1.50  --bmc1_non_equiv_states                 false
% 6.02/1.50  --bmc1_deadlock                         false
% 6.02/1.50  --bmc1_ucm                              false
% 6.02/1.50  --bmc1_add_unsat_core                   none
% 6.02/1.50  --bmc1_unsat_core_children              false
% 6.02/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.02/1.50  --bmc1_out_stat                         full
% 6.02/1.50  --bmc1_ground_init                      false
% 6.02/1.50  --bmc1_pre_inst_next_state              false
% 6.02/1.50  --bmc1_pre_inst_state                   false
% 6.02/1.50  --bmc1_pre_inst_reach_state             false
% 6.02/1.50  --bmc1_out_unsat_core                   false
% 6.02/1.50  --bmc1_aig_witness_out                  false
% 6.02/1.50  --bmc1_verbose                          false
% 6.02/1.50  --bmc1_dump_clauses_tptp                false
% 6.02/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.02/1.50  --bmc1_dump_file                        -
% 6.02/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.02/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.02/1.50  --bmc1_ucm_extend_mode                  1
% 6.02/1.50  --bmc1_ucm_init_mode                    2
% 6.02/1.50  --bmc1_ucm_cone_mode                    none
% 6.02/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.02/1.50  --bmc1_ucm_relax_model                  4
% 6.02/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.02/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.02/1.50  --bmc1_ucm_layered_model                none
% 6.02/1.50  --bmc1_ucm_max_lemma_size               10
% 6.02/1.50  
% 6.02/1.50  ------ AIG Options
% 6.02/1.50  
% 6.02/1.50  --aig_mode                              false
% 6.02/1.50  
% 6.02/1.50  ------ Instantiation Options
% 6.02/1.50  
% 6.02/1.50  --instantiation_flag                    true
% 6.02/1.50  --inst_sos_flag                         false
% 6.02/1.50  --inst_sos_phase                        true
% 6.02/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.02/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.02/1.50  --inst_lit_sel_side                     num_symb
% 6.02/1.50  --inst_solver_per_active                1400
% 6.02/1.50  --inst_solver_calls_frac                1.
% 6.02/1.50  --inst_passive_queue_type               priority_queues
% 6.02/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.02/1.50  --inst_passive_queues_freq              [25;2]
% 6.02/1.50  --inst_dismatching                      true
% 6.02/1.50  --inst_eager_unprocessed_to_passive     true
% 6.02/1.50  --inst_prop_sim_given                   true
% 6.02/1.50  --inst_prop_sim_new                     false
% 6.02/1.50  --inst_subs_new                         false
% 6.02/1.50  --inst_eq_res_simp                      false
% 6.02/1.50  --inst_subs_given                       false
% 6.02/1.50  --inst_orphan_elimination               true
% 6.02/1.50  --inst_learning_loop_flag               true
% 6.02/1.50  --inst_learning_start                   3000
% 6.02/1.50  --inst_learning_factor                  2
% 6.02/1.50  --inst_start_prop_sim_after_learn       3
% 6.02/1.50  --inst_sel_renew                        solver
% 6.02/1.50  --inst_lit_activity_flag                true
% 6.02/1.50  --inst_restr_to_given                   false
% 6.02/1.50  --inst_activity_threshold               500
% 6.02/1.50  --inst_out_proof                        true
% 6.02/1.50  
% 6.02/1.50  ------ Resolution Options
% 6.02/1.50  
% 6.02/1.50  --resolution_flag                       true
% 6.02/1.50  --res_lit_sel                           adaptive
% 6.02/1.50  --res_lit_sel_side                      none
% 6.02/1.50  --res_ordering                          kbo
% 6.02/1.50  --res_to_prop_solver                    active
% 6.02/1.50  --res_prop_simpl_new                    false
% 6.02/1.50  --res_prop_simpl_given                  true
% 6.02/1.50  --res_passive_queue_type                priority_queues
% 6.02/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.02/1.50  --res_passive_queues_freq               [15;5]
% 6.02/1.50  --res_forward_subs                      full
% 6.02/1.50  --res_backward_subs                     full
% 6.02/1.50  --res_forward_subs_resolution           true
% 6.02/1.50  --res_backward_subs_resolution          true
% 6.02/1.50  --res_orphan_elimination                true
% 6.02/1.50  --res_time_limit                        2.
% 6.02/1.50  --res_out_proof                         true
% 6.02/1.50  
% 6.02/1.50  ------ Superposition Options
% 6.02/1.50  
% 6.02/1.50  --superposition_flag                    true
% 6.02/1.50  --sup_passive_queue_type                priority_queues
% 6.02/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.02/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.02/1.50  --demod_completeness_check              fast
% 6.02/1.50  --demod_use_ground                      true
% 6.02/1.50  --sup_to_prop_solver                    passive
% 6.02/1.50  --sup_prop_simpl_new                    true
% 6.02/1.50  --sup_prop_simpl_given                  true
% 6.02/1.50  --sup_fun_splitting                     false
% 6.02/1.50  --sup_smt_interval                      50000
% 6.02/1.50  
% 6.02/1.50  ------ Superposition Simplification Setup
% 6.02/1.50  
% 6.02/1.50  --sup_indices_passive                   []
% 6.02/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.02/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.02/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.02/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.02/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.02/1.50  --sup_full_bw                           [BwDemod]
% 6.02/1.50  --sup_immed_triv                        [TrivRules]
% 6.02/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.02/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.02/1.50  --sup_immed_bw_main                     []
% 6.02/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.02/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.02/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.02/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.02/1.50  
% 6.02/1.50  ------ Combination Options
% 6.02/1.50  
% 6.02/1.50  --comb_res_mult                         3
% 6.02/1.50  --comb_sup_mult                         2
% 6.02/1.50  --comb_inst_mult                        10
% 6.02/1.50  
% 6.02/1.50  ------ Debug Options
% 6.02/1.50  
% 6.02/1.50  --dbg_backtrace                         false
% 6.02/1.50  --dbg_dump_prop_clauses                 false
% 6.02/1.50  --dbg_dump_prop_clauses_file            -
% 6.02/1.50  --dbg_out_stat                          false
% 6.02/1.50  ------ Parsing...
% 6.02/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.02/1.50  
% 6.02/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.02/1.50  
% 6.02/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.02/1.50  
% 6.02/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.02/1.50  ------ Proving...
% 6.02/1.50  ------ Problem Properties 
% 6.02/1.50  
% 6.02/1.50  
% 6.02/1.50  clauses                                 70
% 6.02/1.50  conjectures                             6
% 6.02/1.50  EPR                                     3
% 6.02/1.50  Horn                                    59
% 6.02/1.50  unary                                   16
% 6.02/1.50  binary                                  11
% 6.02/1.50  lits                                    192
% 6.02/1.50  lits eq                                 53
% 6.02/1.50  fd_pure                                 0
% 6.02/1.50  fd_pseudo                               0
% 6.02/1.50  fd_cond                                 7
% 6.02/1.50  fd_pseudo_cond                          1
% 6.02/1.50  AC symbols                              0
% 6.02/1.50  
% 6.02/1.50  ------ Schedule dynamic 5 is on 
% 6.02/1.50  
% 6.02/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.02/1.50  
% 6.02/1.50  
% 6.02/1.50  ------ 
% 6.02/1.50  Current options:
% 6.02/1.50  ------ 
% 6.02/1.50  
% 6.02/1.50  ------ Input Options
% 6.02/1.50  
% 6.02/1.50  --out_options                           all
% 6.02/1.50  --tptp_safe_out                         true
% 6.02/1.50  --problem_path                          ""
% 6.02/1.50  --include_path                          ""
% 6.02/1.50  --clausifier                            res/vclausify_rel
% 6.02/1.50  --clausifier_options                    --mode clausify
% 6.02/1.50  --stdin                                 false
% 6.02/1.50  --stats_out                             all
% 6.02/1.50  
% 6.02/1.50  ------ General Options
% 6.02/1.50  
% 6.02/1.50  --fof                                   false
% 6.02/1.50  --time_out_real                         305.
% 6.02/1.50  --time_out_virtual                      -1.
% 6.02/1.50  --symbol_type_check                     false
% 6.02/1.50  --clausify_out                          false
% 6.02/1.50  --sig_cnt_out                           false
% 6.02/1.50  --trig_cnt_out                          false
% 6.02/1.50  --trig_cnt_out_tolerance                1.
% 6.02/1.50  --trig_cnt_out_sk_spl                   false
% 6.02/1.50  --abstr_cl_out                          false
% 6.02/1.50  
% 6.02/1.50  ------ Global Options
% 6.02/1.50  
% 6.02/1.50  --schedule                              default
% 6.02/1.50  --add_important_lit                     false
% 6.02/1.50  --prop_solver_per_cl                    1000
% 6.02/1.50  --min_unsat_core                        false
% 6.02/1.50  --soft_assumptions                      false
% 6.02/1.50  --soft_lemma_size                       3
% 6.02/1.50  --prop_impl_unit_size                   0
% 6.02/1.50  --prop_impl_unit                        []
% 6.02/1.50  --share_sel_clauses                     true
% 6.02/1.50  --reset_solvers                         false
% 6.02/1.50  --bc_imp_inh                            [conj_cone]
% 6.02/1.50  --conj_cone_tolerance                   3.
% 6.02/1.50  --extra_neg_conj                        none
% 6.02/1.50  --large_theory_mode                     true
% 6.02/1.50  --prolific_symb_bound                   200
% 6.02/1.50  --lt_threshold                          2000
% 6.02/1.50  --clause_weak_htbl                      true
% 6.02/1.50  --gc_record_bc_elim                     false
% 6.02/1.50  
% 6.02/1.50  ------ Preprocessing Options
% 6.02/1.50  
% 6.02/1.50  --preprocessing_flag                    true
% 6.02/1.50  --time_out_prep_mult                    0.1
% 6.02/1.50  --splitting_mode                        input
% 6.02/1.50  --splitting_grd                         true
% 6.02/1.50  --splitting_cvd                         false
% 6.02/1.50  --splitting_cvd_svl                     false
% 6.02/1.50  --splitting_nvd                         32
% 6.02/1.50  --sub_typing                            true
% 6.02/1.50  --prep_gs_sim                           true
% 6.02/1.50  --prep_unflatten                        true
% 6.02/1.50  --prep_res_sim                          true
% 6.02/1.50  --prep_upred                            true
% 6.02/1.50  --prep_sem_filter                       exhaustive
% 6.02/1.50  --prep_sem_filter_out                   false
% 6.02/1.50  --pred_elim                             true
% 6.02/1.50  --res_sim_input                         true
% 6.02/1.50  --eq_ax_congr_red                       true
% 6.02/1.50  --pure_diseq_elim                       true
% 6.02/1.50  --brand_transform                       false
% 6.02/1.50  --non_eq_to_eq                          false
% 6.02/1.50  --prep_def_merge                        true
% 6.02/1.50  --prep_def_merge_prop_impl              false
% 6.02/1.50  --prep_def_merge_mbd                    true
% 6.02/1.50  --prep_def_merge_tr_red                 false
% 6.02/1.50  --prep_def_merge_tr_cl                  false
% 6.02/1.50  --smt_preprocessing                     true
% 6.02/1.50  --smt_ac_axioms                         fast
% 6.02/1.50  --preprocessed_out                      false
% 6.02/1.50  --preprocessed_stats                    false
% 6.02/1.50  
% 6.02/1.50  ------ Abstraction refinement Options
% 6.02/1.50  
% 6.02/1.50  --abstr_ref                             []
% 6.02/1.50  --abstr_ref_prep                        false
% 6.02/1.50  --abstr_ref_until_sat                   false
% 6.02/1.50  --abstr_ref_sig_restrict                funpre
% 6.02/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.02/1.50  --abstr_ref_under                       []
% 6.02/1.50  
% 6.02/1.50  ------ SAT Options
% 6.02/1.50  
% 6.02/1.50  --sat_mode                              false
% 6.02/1.50  --sat_fm_restart_options                ""
% 6.02/1.50  --sat_gr_def                            false
% 6.02/1.50  --sat_epr_types                         true
% 6.02/1.50  --sat_non_cyclic_types                  false
% 6.02/1.50  --sat_finite_models                     false
% 6.02/1.50  --sat_fm_lemmas                         false
% 6.02/1.50  --sat_fm_prep                           false
% 6.02/1.50  --sat_fm_uc_incr                        true
% 6.02/1.50  --sat_out_model                         small
% 6.02/1.50  --sat_out_clauses                       false
% 6.02/1.50  
% 6.02/1.50  ------ QBF Options
% 6.02/1.50  
% 6.02/1.50  --qbf_mode                              false
% 6.02/1.50  --qbf_elim_univ                         false
% 6.02/1.50  --qbf_dom_inst                          none
% 6.02/1.50  --qbf_dom_pre_inst                      false
% 6.02/1.50  --qbf_sk_in                             false
% 6.02/1.50  --qbf_pred_elim                         true
% 6.02/1.50  --qbf_split                             512
% 6.02/1.50  
% 6.02/1.50  ------ BMC1 Options
% 6.02/1.50  
% 6.02/1.50  --bmc1_incremental                      false
% 6.02/1.50  --bmc1_axioms                           reachable_all
% 6.02/1.50  --bmc1_min_bound                        0
% 6.02/1.50  --bmc1_max_bound                        -1
% 6.02/1.50  --bmc1_max_bound_default                -1
% 6.02/1.50  --bmc1_symbol_reachability              true
% 6.02/1.50  --bmc1_property_lemmas                  false
% 6.02/1.50  --bmc1_k_induction                      false
% 6.02/1.50  --bmc1_non_equiv_states                 false
% 6.02/1.50  --bmc1_deadlock                         false
% 6.02/1.50  --bmc1_ucm                              false
% 6.02/1.50  --bmc1_add_unsat_core                   none
% 6.02/1.50  --bmc1_unsat_core_children              false
% 6.02/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.02/1.50  --bmc1_out_stat                         full
% 6.02/1.50  --bmc1_ground_init                      false
% 6.02/1.50  --bmc1_pre_inst_next_state              false
% 6.02/1.50  --bmc1_pre_inst_state                   false
% 6.02/1.50  --bmc1_pre_inst_reach_state             false
% 6.02/1.50  --bmc1_out_unsat_core                   false
% 6.02/1.50  --bmc1_aig_witness_out                  false
% 6.02/1.50  --bmc1_verbose                          false
% 6.02/1.50  --bmc1_dump_clauses_tptp                false
% 6.02/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.02/1.50  --bmc1_dump_file                        -
% 6.02/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.02/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.02/1.50  --bmc1_ucm_extend_mode                  1
% 6.02/1.50  --bmc1_ucm_init_mode                    2
% 6.02/1.50  --bmc1_ucm_cone_mode                    none
% 6.02/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.02/1.50  --bmc1_ucm_relax_model                  4
% 6.02/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.02/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.02/1.50  --bmc1_ucm_layered_model                none
% 6.02/1.50  --bmc1_ucm_max_lemma_size               10
% 6.02/1.50  
% 6.02/1.50  ------ AIG Options
% 6.02/1.50  
% 6.02/1.50  --aig_mode                              false
% 6.02/1.50  
% 6.02/1.50  ------ Instantiation Options
% 6.02/1.50  
% 6.02/1.50  --instantiation_flag                    true
% 6.02/1.50  --inst_sos_flag                         false
% 6.02/1.50  --inst_sos_phase                        true
% 6.02/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.02/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.02/1.50  --inst_lit_sel_side                     none
% 6.02/1.50  --inst_solver_per_active                1400
% 6.02/1.50  --inst_solver_calls_frac                1.
% 6.02/1.50  --inst_passive_queue_type               priority_queues
% 6.02/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.02/1.50  --inst_passive_queues_freq              [25;2]
% 6.02/1.50  --inst_dismatching                      true
% 6.02/1.50  --inst_eager_unprocessed_to_passive     true
% 6.02/1.50  --inst_prop_sim_given                   true
% 6.02/1.50  --inst_prop_sim_new                     false
% 6.02/1.50  --inst_subs_new                         false
% 6.02/1.50  --inst_eq_res_simp                      false
% 6.02/1.50  --inst_subs_given                       false
% 6.02/1.50  --inst_orphan_elimination               true
% 6.02/1.50  --inst_learning_loop_flag               true
% 6.02/1.50  --inst_learning_start                   3000
% 6.02/1.50  --inst_learning_factor                  2
% 6.02/1.50  --inst_start_prop_sim_after_learn       3
% 6.02/1.50  --inst_sel_renew                        solver
% 6.02/1.50  --inst_lit_activity_flag                true
% 6.02/1.50  --inst_restr_to_given                   false
% 6.02/1.50  --inst_activity_threshold               500
% 6.02/1.50  --inst_out_proof                        true
% 6.02/1.50  
% 6.02/1.50  ------ Resolution Options
% 6.02/1.50  
% 6.02/1.50  --resolution_flag                       false
% 6.02/1.50  --res_lit_sel                           adaptive
% 6.02/1.50  --res_lit_sel_side                      none
% 6.02/1.50  --res_ordering                          kbo
% 6.02/1.50  --res_to_prop_solver                    active
% 6.02/1.50  --res_prop_simpl_new                    false
% 6.02/1.50  --res_prop_simpl_given                  true
% 6.02/1.50  --res_passive_queue_type                priority_queues
% 6.02/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.02/1.50  --res_passive_queues_freq               [15;5]
% 6.02/1.50  --res_forward_subs                      full
% 6.02/1.50  --res_backward_subs                     full
% 6.02/1.50  --res_forward_subs_resolution           true
% 6.02/1.50  --res_backward_subs_resolution          true
% 6.02/1.50  --res_orphan_elimination                true
% 6.02/1.50  --res_time_limit                        2.
% 6.02/1.50  --res_out_proof                         true
% 6.02/1.50  
% 6.02/1.50  ------ Superposition Options
% 6.02/1.50  
% 6.02/1.50  --superposition_flag                    true
% 6.02/1.50  --sup_passive_queue_type                priority_queues
% 6.02/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.02/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.02/1.50  --demod_completeness_check              fast
% 6.02/1.50  --demod_use_ground                      true
% 6.02/1.50  --sup_to_prop_solver                    passive
% 6.02/1.50  --sup_prop_simpl_new                    true
% 6.02/1.50  --sup_prop_simpl_given                  true
% 6.02/1.50  --sup_fun_splitting                     false
% 6.02/1.50  --sup_smt_interval                      50000
% 6.02/1.50  
% 6.02/1.50  ------ Superposition Simplification Setup
% 6.02/1.50  
% 6.02/1.50  --sup_indices_passive                   []
% 6.02/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.02/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.02/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.02/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.02/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.02/1.50  --sup_full_bw                           [BwDemod]
% 6.02/1.50  --sup_immed_triv                        [TrivRules]
% 6.02/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.02/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.02/1.50  --sup_immed_bw_main                     []
% 6.02/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.02/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.02/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.02/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.02/1.50  
% 6.02/1.50  ------ Combination Options
% 6.02/1.50  
% 6.02/1.50  --comb_res_mult                         3
% 6.02/1.50  --comb_sup_mult                         2
% 6.02/1.50  --comb_inst_mult                        10
% 6.02/1.50  
% 6.02/1.50  ------ Debug Options
% 6.02/1.50  
% 6.02/1.50  --dbg_backtrace                         false
% 6.02/1.50  --dbg_dump_prop_clauses                 false
% 6.02/1.50  --dbg_dump_prop_clauses_file            -
% 6.02/1.50  --dbg_out_stat                          false
% 6.02/1.50  
% 6.02/1.50  
% 6.02/1.50  
% 6.02/1.50  
% 6.02/1.50  ------ Proving...
% 6.02/1.50  
% 6.02/1.50  
% 6.02/1.50  % SZS status Theorem for theBenchmark.p
% 6.02/1.50  
% 6.02/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 6.02/1.50  
% 6.02/1.50  fof(f44,conjecture,(
% 6.02/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 6.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.02/1.50  
% 6.02/1.50  fof(f45,negated_conjecture,(
% 6.02/1.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 6.02/1.50    inference(negated_conjecture,[],[f44])).
% 6.02/1.50  
% 6.02/1.50  fof(f83,plain,(
% 6.02/1.50    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 6.02/1.50    inference(ennf_transformation,[],[f45])).
% 6.02/1.50  
% 6.02/1.50  fof(f84,plain,(
% 6.02/1.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 6.02/1.50    inference(flattening,[],[f83])).
% 6.02/1.50  
% 6.02/1.50  fof(f98,plain,(
% 6.02/1.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))) & k2_relset_1(sK4,sK5,sK6) = sK5 & v2_funct_1(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 6.02/1.50    introduced(choice_axiom,[])).
% 6.02/1.50  
% 6.02/1.50  fof(f99,plain,(
% 6.02/1.50    (~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))) & k2_relset_1(sK4,sK5,sK6) = sK5 & v2_funct_1(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 6.02/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f84,f98])).
% 6.02/1.50  
% 6.02/1.50  fof(f178,plain,(
% 6.02/1.50    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 6.02/1.50    inference(cnf_transformation,[],[f99])).
% 6.02/1.50  
% 6.02/1.50  fof(f37,axiom,(
% 6.02/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 6.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.02/1.50  
% 6.02/1.50  fof(f73,plain,(
% 6.02/1.50    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.02/1.50    inference(ennf_transformation,[],[f37])).
% 6.02/1.50  
% 6.02/1.50  fof(f145,plain,(
% 6.02/1.50    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.02/1.50    inference(cnf_transformation,[],[f73])).
% 6.02/1.50  
% 6.02/1.50  fof(f38,axiom,(
% 6.02/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 6.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.02/1.50  
% 6.02/1.50  fof(f74,plain,(
% 6.02/1.50    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.02/1.50    inference(ennf_transformation,[],[f38])).
% 6.02/1.50  
% 6.02/1.50  fof(f146,plain,(
% 6.02/1.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.02/1.50    inference(cnf_transformation,[],[f74])).
% 6.02/1.50  
% 6.02/1.50  fof(f180,plain,(
% 6.02/1.50    k2_relset_1(sK4,sK5,sK6) = sK5),
% 6.02/1.50    inference(cnf_transformation,[],[f99])).
% 6.02/1.50  
% 6.02/1.50  fof(f29,axiom,(
% 6.02/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 6.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.02/1.50  
% 6.02/1.50  fof(f60,plain,(
% 6.02/1.50    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.02/1.50    inference(ennf_transformation,[],[f29])).
% 6.02/1.50  
% 6.02/1.50  fof(f61,plain,(
% 6.02/1.50    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 6.02/1.50    inference(flattening,[],[f60])).
% 6.02/1.50  
% 6.02/1.50  fof(f136,plain,(
% 6.02/1.50    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.02/1.50    inference(cnf_transformation,[],[f61])).
% 6.02/1.50  
% 6.02/1.50  fof(f36,axiom,(
% 6.02/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 6.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.02/1.50  
% 6.02/1.50  fof(f72,plain,(
% 6.02/1.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.02/1.50    inference(ennf_transformation,[],[f36])).
% 6.02/1.50  
% 6.02/1.50  fof(f144,plain,(
% 6.02/1.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.02/1.50    inference(cnf_transformation,[],[f72])).
% 6.02/1.50  
% 6.02/1.50  fof(f34,axiom,(
% 6.02/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.02/1.50  
% 6.02/1.50  fof(f70,plain,(
% 6.02/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.02/1.50    inference(ennf_transformation,[],[f34])).
% 6.02/1.50  
% 6.02/1.50  fof(f142,plain,(
% 6.02/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.02/1.50    inference(cnf_transformation,[],[f70])).
% 6.02/1.50  
% 6.02/1.50  fof(f21,axiom,(
% 6.02/1.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)))),
% 6.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.02/1.50  
% 6.02/1.50  fof(f48,plain,(
% 6.02/1.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 6.02/1.50    inference(ennf_transformation,[],[f21])).
% 6.02/1.50  
% 6.02/1.50  fof(f122,plain,(
% 6.02/1.50    ( ! [X0] : (k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 6.02/1.50    inference(cnf_transformation,[],[f48])).
% 6.02/1.50  
% 6.02/1.50  fof(f43,axiom,(
% 6.02/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 6.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.02/1.50  
% 6.02/1.50  fof(f81,plain,(
% 6.02/1.50    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.02/1.50    inference(ennf_transformation,[],[f43])).
% 6.02/1.50  
% 6.02/1.50  fof(f82,plain,(
% 6.02/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 6.02/1.50    inference(flattening,[],[f81])).
% 6.02/1.50  
% 6.02/1.50  fof(f175,plain,(
% 6.02/1.50    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.02/1.50    inference(cnf_transformation,[],[f82])).
% 6.02/1.50  
% 6.02/1.50  fof(f123,plain,(
% 6.02/1.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 6.02/1.50    inference(cnf_transformation,[],[f48])).
% 6.02/1.50  
% 6.02/1.50  fof(f176,plain,(
% 6.02/1.50    v1_funct_1(sK6)),
% 6.02/1.50    inference(cnf_transformation,[],[f99])).
% 6.02/1.50  
% 6.02/1.50  fof(f179,plain,(
% 6.02/1.50    v2_funct_1(sK6)),
% 6.02/1.50    inference(cnf_transformation,[],[f99])).
% 6.02/1.50  
% 6.02/1.50  fof(f26,axiom,(
% 6.02/1.50    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))))),
% 6.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.02/1.50  
% 6.02/1.50  fof(f54,plain,(
% 6.02/1.50    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.02/1.50    inference(ennf_transformation,[],[f26])).
% 6.02/1.50  
% 6.02/1.50  fof(f55,plain,(
% 6.02/1.50    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.02/1.50    inference(flattening,[],[f54])).
% 6.02/1.50  
% 6.02/1.50  fof(f131,plain,(
% 6.02/1.50    ( ! [X0] : (v1_funct_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.02/1.50    inference(cnf_transformation,[],[f55])).
% 6.02/1.50  
% 6.02/1.50  fof(f130,plain,(
% 6.02/1.50    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.02/1.50    inference(cnf_transformation,[],[f55])).
% 6.02/1.50  
% 6.02/1.50  fof(f17,axiom,(
% 6.02/1.50    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 6.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.02/1.50  
% 6.02/1.50  fof(f46,plain,(
% 6.02/1.50    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 6.02/1.50    inference(ennf_transformation,[],[f17])).
% 6.02/1.50  
% 6.02/1.50  fof(f118,plain,(
% 6.02/1.50    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 6.02/1.50    inference(cnf_transformation,[],[f46])).
% 6.02/1.50  
% 6.02/1.50  fof(f31,axiom,(
% 6.02/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 6.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.02/1.50  
% 6.02/1.50  fof(f64,plain,(
% 6.02/1.50    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.02/1.50    inference(ennf_transformation,[],[f31])).
% 6.02/1.50  
% 6.02/1.50  fof(f65,plain,(
% 6.02/1.50    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 6.02/1.50    inference(flattening,[],[f64])).
% 6.02/1.50  
% 6.02/1.50  fof(f138,plain,(
% 6.02/1.50    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.02/1.50    inference(cnf_transformation,[],[f65])).
% 6.02/1.50  
% 6.02/1.50  fof(f25,axiom,(
% 6.02/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 6.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.02/1.50  
% 6.02/1.50  fof(f52,plain,(
% 6.02/1.50    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.02/1.50    inference(ennf_transformation,[],[f25])).
% 6.02/1.50  
% 6.02/1.50  fof(f53,plain,(
% 6.02/1.50    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.02/1.50    inference(flattening,[],[f52])).
% 6.02/1.50  
% 6.02/1.50  fof(f129,plain,(
% 6.02/1.50    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.02/1.50    inference(cnf_transformation,[],[f53])).
% 6.02/1.50  
% 6.02/1.50  fof(f181,plain,(
% 6.02/1.50    ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))),
% 6.02/1.50    inference(cnf_transformation,[],[f99])).
% 6.02/1.50  
% 6.02/1.50  fof(f27,axiom,(
% 6.02/1.50    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 6.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.02/1.50  
% 6.02/1.50  fof(f56,plain,(
% 6.02/1.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.02/1.50    inference(ennf_transformation,[],[f27])).
% 6.02/1.50  
% 6.02/1.50  fof(f57,plain,(
% 6.02/1.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.02/1.50    inference(flattening,[],[f56])).
% 6.02/1.50  
% 6.02/1.50  fof(f133,plain,(
% 6.02/1.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.02/1.50    inference(cnf_transformation,[],[f57])).
% 6.02/1.50  
% 6.02/1.50  fof(f174,plain,(
% 6.02/1.50    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.02/1.50    inference(cnf_transformation,[],[f82])).
% 6.02/1.50  
% 6.02/1.50  cnf(c_69,negated_conjecture,
% 6.02/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 6.02/1.50      inference(cnf_transformation,[],[f178]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_10896,plain,
% 6.02/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_69]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_35,plain,
% 6.02/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.02/1.50      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 6.02/1.50      inference(cnf_transformation,[],[f145]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_10927,plain,
% 6.02/1.50      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 6.02/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_17063,plain,
% 6.02/1.50      ( k7_relset_1(sK4,sK5,sK6,X0) = k9_relat_1(sK6,X0) ),
% 6.02/1.50      inference(superposition,[status(thm)],[c_10896,c_10927]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_37,plain,
% 6.02/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.02/1.50      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 6.02/1.50      inference(cnf_transformation,[],[f146]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_10925,plain,
% 6.02/1.50      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 6.02/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_18183,plain,
% 6.02/1.50      ( k7_relset_1(sK4,sK5,sK6,sK4) = k2_relset_1(sK4,sK5,sK6) ),
% 6.02/1.50      inference(superposition,[status(thm)],[c_10896,c_10925]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_67,negated_conjecture,
% 6.02/1.50      ( k2_relset_1(sK4,sK5,sK6) = sK5 ),
% 6.02/1.50      inference(cnf_transformation,[],[f180]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_18215,plain,
% 6.02/1.50      ( k7_relset_1(sK4,sK5,sK6,sK4) = sK5 ),
% 6.02/1.50      inference(light_normalisation,[status(thm)],[c_18183,c_67]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_18250,plain,
% 6.02/1.50      ( k9_relat_1(sK6,sK4) = sK5 ),
% 6.02/1.50      inference(superposition,[status(thm)],[c_17063,c_18215]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_26,plain,
% 6.02/1.50      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 6.02/1.50      | ~ v1_funct_1(X0)
% 6.02/1.50      | ~ v2_funct_1(X0)
% 6.02/1.50      | ~ v1_relat_1(X0) ),
% 6.02/1.50      inference(cnf_transformation,[],[f136]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_10936,plain,
% 6.02/1.50      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) = iProver_top
% 6.02/1.50      | v1_funct_1(X0) != iProver_top
% 6.02/1.50      | v2_funct_1(X0) != iProver_top
% 6.02/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_24999,plain,
% 6.02/1.50      ( r1_tarski(k10_relat_1(sK6,sK5),sK4) = iProver_top
% 6.02/1.50      | v1_funct_1(sK6) != iProver_top
% 6.02/1.50      | v2_funct_1(sK6) != iProver_top
% 6.02/1.50      | v1_relat_1(sK6) != iProver_top ),
% 6.02/1.50      inference(superposition,[status(thm)],[c_18250,c_10936]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_34,plain,
% 6.02/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.02/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 6.02/1.50      inference(cnf_transformation,[],[f144]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_10928,plain,
% 6.02/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 6.02/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_14536,plain,
% 6.02/1.50      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 6.02/1.50      inference(superposition,[status(thm)],[c_10896,c_10928]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_14576,plain,
% 6.02/1.50      ( k2_relat_1(sK6) = sK5 ),
% 6.02/1.50      inference(light_normalisation,[status(thm)],[c_14536,c_67]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_32,plain,
% 6.02/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.02/1.50      | v1_relat_1(X0) ),
% 6.02/1.50      inference(cnf_transformation,[],[f142]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_10930,plain,
% 6.02/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.02/1.50      | v1_relat_1(X0) = iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_11954,plain,
% 6.02/1.50      ( v1_relat_1(sK6) = iProver_top ),
% 6.02/1.50      inference(superposition,[status(thm)],[c_10896,c_10930]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_13,plain,
% 6.02/1.50      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 6.02/1.50      inference(cnf_transformation,[],[f122]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_10948,plain,
% 6.02/1.50      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 6.02/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_12107,plain,
% 6.02/1.50      ( k1_relat_1(k4_relat_1(sK6)) = k2_relat_1(sK6) ),
% 6.02/1.50      inference(superposition,[status(thm)],[c_11954,c_10948]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_63,plain,
% 6.02/1.50      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 6.02/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 6.02/1.50      | ~ v1_funct_1(X0)
% 6.02/1.50      | ~ v1_relat_1(X0) ),
% 6.02/1.50      inference(cnf_transformation,[],[f175]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_10900,plain,
% 6.02/1.50      ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 6.02/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 6.02/1.50      | v1_funct_1(X0) != iProver_top
% 6.02/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_12126,plain,
% 6.02/1.50      ( r1_tarski(k2_relat_1(k4_relat_1(sK6)),X0) != iProver_top
% 6.02/1.50      | m1_subset_1(k4_relat_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK6),X0))) = iProver_top
% 6.02/1.50      | v1_funct_1(k4_relat_1(sK6)) != iProver_top
% 6.02/1.50      | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
% 6.02/1.50      inference(superposition,[status(thm)],[c_12107,c_10900]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_12,plain,
% 6.02/1.50      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 6.02/1.50      inference(cnf_transformation,[],[f123]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_10949,plain,
% 6.02/1.50      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 6.02/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_12106,plain,
% 6.02/1.50      ( k2_relat_1(k4_relat_1(sK6)) = k1_relat_1(sK6) ),
% 6.02/1.50      inference(superposition,[status(thm)],[c_11954,c_10949]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_12141,plain,
% 6.02/1.50      ( r1_tarski(k1_relat_1(sK6),X0) != iProver_top
% 6.02/1.50      | m1_subset_1(k4_relat_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK6),X0))) = iProver_top
% 6.02/1.50      | v1_funct_1(k4_relat_1(sK6)) != iProver_top
% 6.02/1.50      | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
% 6.02/1.50      inference(light_normalisation,[status(thm)],[c_12126,c_12106]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_71,negated_conjecture,
% 6.02/1.50      ( v1_funct_1(sK6) ),
% 6.02/1.50      inference(cnf_transformation,[],[f176]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_72,plain,
% 6.02/1.50      ( v1_funct_1(sK6) = iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_74,plain,
% 6.02/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_69]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_68,negated_conjecture,
% 6.02/1.50      ( v2_funct_1(sK6) ),
% 6.02/1.50      inference(cnf_transformation,[],[f179]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_75,plain,
% 6.02/1.50      ( v2_funct_1(sK6) = iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_68]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_20,plain,
% 6.02/1.50      ( ~ v1_funct_1(X0)
% 6.02/1.50      | v1_funct_1(k4_relat_1(X0))
% 6.02/1.50      | ~ v2_funct_1(X0)
% 6.02/1.50      | ~ v1_relat_1(X0) ),
% 6.02/1.50      inference(cnf_transformation,[],[f131]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_11497,plain,
% 6.02/1.50      ( v1_funct_1(k4_relat_1(sK6))
% 6.02/1.50      | ~ v1_funct_1(sK6)
% 6.02/1.50      | ~ v2_funct_1(sK6)
% 6.02/1.50      | ~ v1_relat_1(sK6) ),
% 6.02/1.50      inference(instantiation,[status(thm)],[c_20]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_11498,plain,
% 6.02/1.50      ( v1_funct_1(k4_relat_1(sK6)) = iProver_top
% 6.02/1.50      | v1_funct_1(sK6) != iProver_top
% 6.02/1.50      | v2_funct_1(sK6) != iProver_top
% 6.02/1.50      | v1_relat_1(sK6) != iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_11497]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_21,plain,
% 6.02/1.50      ( ~ v1_funct_1(X0)
% 6.02/1.50      | ~ v2_funct_1(X0)
% 6.02/1.50      | ~ v1_relat_1(X0)
% 6.02/1.50      | v1_relat_1(k4_relat_1(X0)) ),
% 6.02/1.50      inference(cnf_transformation,[],[f130]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_11500,plain,
% 6.02/1.50      ( ~ v1_funct_1(sK6)
% 6.02/1.50      | ~ v2_funct_1(sK6)
% 6.02/1.50      | v1_relat_1(k4_relat_1(sK6))
% 6.02/1.50      | ~ v1_relat_1(sK6) ),
% 6.02/1.50      inference(instantiation,[status(thm)],[c_21]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_11501,plain,
% 6.02/1.50      ( v1_funct_1(sK6) != iProver_top
% 6.02/1.50      | v2_funct_1(sK6) != iProver_top
% 6.02/1.50      | v1_relat_1(k4_relat_1(sK6)) = iProver_top
% 6.02/1.50      | v1_relat_1(sK6) != iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_11500]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_11514,plain,
% 6.02/1.50      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 6.02/1.50      | v1_relat_1(sK6) ),
% 6.02/1.50      inference(instantiation,[status(thm)],[c_32]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_11515,plain,
% 6.02/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 6.02/1.50      | v1_relat_1(sK6) = iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_11514]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_12165,plain,
% 6.02/1.50      ( r1_tarski(k1_relat_1(sK6),X0) != iProver_top
% 6.02/1.50      | m1_subset_1(k4_relat_1(sK6),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK6),X0))) = iProver_top ),
% 6.02/1.50      inference(global_propositional_subsumption,
% 6.02/1.50                [status(thm)],
% 6.02/1.50                [c_12141,c_72,c_74,c_75,c_11498,c_11501,c_11515]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_12174,plain,
% 6.02/1.50      ( r1_tarski(k1_relat_1(sK6),X0) != iProver_top
% 6.02/1.50      | v1_relat_1(k4_relat_1(sK6)) = iProver_top ),
% 6.02/1.50      inference(superposition,[status(thm)],[c_12165,c_10930]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_12286,plain,
% 6.02/1.50      ( v1_relat_1(k4_relat_1(sK6)) = iProver_top ),
% 6.02/1.50      inference(global_propositional_subsumption,
% 6.02/1.50                [status(thm)],
% 6.02/1.50                [c_12174,c_72,c_74,c_75,c_11501,c_11515]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_8,plain,
% 6.02/1.50      ( ~ v1_relat_1(X0)
% 6.02/1.50      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 6.02/1.50      inference(cnf_transformation,[],[f118]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_10951,plain,
% 6.02/1.50      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 6.02/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_12291,plain,
% 6.02/1.50      ( k9_relat_1(k4_relat_1(sK6),k1_relat_1(k4_relat_1(sK6))) = k2_relat_1(k4_relat_1(sK6)) ),
% 6.02/1.50      inference(superposition,[status(thm)],[c_12286,c_10951]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_12301,plain,
% 6.02/1.50      ( k9_relat_1(k4_relat_1(sK6),k2_relat_1(sK6)) = k1_relat_1(sK6) ),
% 6.02/1.50      inference(light_normalisation,
% 6.02/1.50                [status(thm)],
% 6.02/1.50                [c_12291,c_12106,c_12107]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_14687,plain,
% 6.02/1.50      ( k9_relat_1(k4_relat_1(sK6),sK5) = k1_relat_1(sK6) ),
% 6.02/1.50      inference(demodulation,[status(thm)],[c_14576,c_12301]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_10894,plain,
% 6.02/1.50      ( v1_funct_1(sK6) = iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_28,plain,
% 6.02/1.50      ( ~ v1_funct_1(X0)
% 6.02/1.50      | ~ v2_funct_1(X0)
% 6.02/1.50      | ~ v1_relat_1(X0)
% 6.02/1.50      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 6.02/1.50      inference(cnf_transformation,[],[f138]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_10934,plain,
% 6.02/1.50      ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 6.02/1.50      | v1_funct_1(X0) != iProver_top
% 6.02/1.50      | v2_funct_1(X0) != iProver_top
% 6.02/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_23928,plain,
% 6.02/1.50      ( k9_relat_1(k2_funct_1(sK6),X0) = k10_relat_1(sK6,X0)
% 6.02/1.50      | v2_funct_1(sK6) != iProver_top
% 6.02/1.50      | v1_relat_1(sK6) != iProver_top ),
% 6.02/1.50      inference(superposition,[status(thm)],[c_10894,c_10934]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_11580,plain,
% 6.02/1.50      ( ~ v1_funct_1(sK6)
% 6.02/1.50      | ~ v2_funct_1(sK6)
% 6.02/1.50      | ~ v1_relat_1(sK6)
% 6.02/1.50      | k9_relat_1(k2_funct_1(sK6),X0) = k10_relat_1(sK6,X0) ),
% 6.02/1.50      inference(instantiation,[status(thm)],[c_28]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_24296,plain,
% 6.02/1.50      ( k9_relat_1(k2_funct_1(sK6),X0) = k10_relat_1(sK6,X0) ),
% 6.02/1.50      inference(global_propositional_subsumption,
% 6.02/1.50                [status(thm)],
% 6.02/1.50                [c_23928,c_71,c_69,c_68,c_11514,c_11580]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_19,plain,
% 6.02/1.50      ( ~ v1_funct_1(X0)
% 6.02/1.50      | ~ v2_funct_1(X0)
% 6.02/1.50      | ~ v1_relat_1(X0)
% 6.02/1.50      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 6.02/1.50      inference(cnf_transformation,[],[f129]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_10943,plain,
% 6.02/1.50      ( k2_funct_1(X0) = k4_relat_1(X0)
% 6.02/1.50      | v1_funct_1(X0) != iProver_top
% 6.02/1.50      | v2_funct_1(X0) != iProver_top
% 6.02/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_23991,plain,
% 6.02/1.50      ( k2_funct_1(sK6) = k4_relat_1(sK6)
% 6.02/1.50      | v2_funct_1(sK6) != iProver_top
% 6.02/1.50      | v1_relat_1(sK6) != iProver_top ),
% 6.02/1.50      inference(superposition,[status(thm)],[c_10894,c_10943]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_11544,plain,
% 6.02/1.50      ( ~ v1_funct_1(sK6)
% 6.02/1.50      | ~ v2_funct_1(sK6)
% 6.02/1.50      | ~ v1_relat_1(sK6)
% 6.02/1.50      | k2_funct_1(sK6) = k4_relat_1(sK6) ),
% 6.02/1.50      inference(instantiation,[status(thm)],[c_19]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_24247,plain,
% 6.02/1.50      ( k2_funct_1(sK6) = k4_relat_1(sK6) ),
% 6.02/1.50      inference(global_propositional_subsumption,
% 6.02/1.50                [status(thm)],
% 6.02/1.50                [c_23991,c_71,c_69,c_68,c_11514,c_11544]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_24299,plain,
% 6.02/1.50      ( k9_relat_1(k4_relat_1(sK6),X0) = k10_relat_1(sK6,X0) ),
% 6.02/1.50      inference(light_normalisation,[status(thm)],[c_24296,c_24247]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_24314,plain,
% 6.02/1.50      ( k10_relat_1(sK6,sK5) = k1_relat_1(sK6) ),
% 6.02/1.50      inference(superposition,[status(thm)],[c_14687,c_24299]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_25004,plain,
% 6.02/1.50      ( r1_tarski(k1_relat_1(sK6),sK4) = iProver_top
% 6.02/1.50      | v1_funct_1(sK6) != iProver_top
% 6.02/1.50      | v2_funct_1(sK6) != iProver_top
% 6.02/1.50      | v1_relat_1(sK6) != iProver_top ),
% 6.02/1.50      inference(light_normalisation,[status(thm)],[c_24999,c_24314]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_14689,plain,
% 6.02/1.50      ( r1_tarski(k1_relat_1(sK6),X0) != iProver_top
% 6.02/1.50      | m1_subset_1(k4_relat_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top ),
% 6.02/1.50      inference(demodulation,[status(thm)],[c_14576,c_12165]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_66,negated_conjecture,
% 6.02/1.50      ( ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
% 6.02/1.50      | ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 6.02/1.50      | ~ v1_funct_1(k2_funct_1(sK6)) ),
% 6.02/1.50      inference(cnf_transformation,[],[f181]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_10898,plain,
% 6.02/1.50      ( v1_funct_2(k2_funct_1(sK6),sK5,sK4) != iProver_top
% 6.02/1.50      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 6.02/1.50      | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_66]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_76,plain,
% 6.02/1.50      ( v1_funct_2(k2_funct_1(sK6),sK5,sK4) != iProver_top
% 6.02/1.50      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 6.02/1.50      | v1_funct_1(k2_funct_1(sK6)) != iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_66]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_23,plain,
% 6.02/1.50      ( ~ v1_funct_1(X0)
% 6.02/1.50      | v1_funct_1(k2_funct_1(X0))
% 6.02/1.50      | ~ v2_funct_1(X0)
% 6.02/1.50      | ~ v1_relat_1(X0) ),
% 6.02/1.50      inference(cnf_transformation,[],[f133]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_11517,plain,
% 6.02/1.50      ( v1_funct_1(k2_funct_1(sK6))
% 6.02/1.50      | ~ v1_funct_1(sK6)
% 6.02/1.50      | ~ v2_funct_1(sK6)
% 6.02/1.50      | ~ v1_relat_1(sK6) ),
% 6.02/1.50      inference(instantiation,[status(thm)],[c_23]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_11518,plain,
% 6.02/1.50      ( v1_funct_1(k2_funct_1(sK6)) = iProver_top
% 6.02/1.50      | v1_funct_1(sK6) != iProver_top
% 6.02/1.50      | v2_funct_1(sK6) != iProver_top
% 6.02/1.50      | v1_relat_1(sK6) != iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_11517]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_11526,plain,
% 6.02/1.50      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 6.02/1.50      | v1_funct_2(k2_funct_1(sK6),sK5,sK4) != iProver_top ),
% 6.02/1.50      inference(global_propositional_subsumption,
% 6.02/1.50                [status(thm)],
% 6.02/1.50                [c_10898,c_72,c_74,c_75,c_76,c_11515,c_11518]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_11527,plain,
% 6.02/1.50      ( v1_funct_2(k2_funct_1(sK6),sK5,sK4) != iProver_top
% 6.02/1.50      | m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
% 6.02/1.50      inference(renaming,[status(thm)],[c_11526]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_24260,plain,
% 6.02/1.50      ( v1_funct_2(k4_relat_1(sK6),sK5,sK4) != iProver_top
% 6.02/1.50      | m1_subset_1(k4_relat_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top ),
% 6.02/1.50      inference(demodulation,[status(thm)],[c_24247,c_11527]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_24287,plain,
% 6.02/1.50      ( v1_funct_2(k4_relat_1(sK6),sK5,sK4) != iProver_top
% 6.02/1.50      | r1_tarski(k1_relat_1(sK6),sK4) != iProver_top ),
% 6.02/1.50      inference(superposition,[status(thm)],[c_14689,c_24260]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_64,plain,
% 6.02/1.50      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 6.02/1.50      | ~ r1_tarski(k2_relat_1(X0),X1)
% 6.02/1.50      | ~ v1_funct_1(X0)
% 6.02/1.50      | ~ v1_relat_1(X0) ),
% 6.02/1.50      inference(cnf_transformation,[],[f174]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_10899,plain,
% 6.02/1.50      ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
% 6.02/1.50      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 6.02/1.50      | v1_funct_1(X0) != iProver_top
% 6.02/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.02/1.50      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_12127,plain,
% 6.02/1.50      ( v1_funct_2(k4_relat_1(sK6),k2_relat_1(sK6),X0) = iProver_top
% 6.02/1.50      | r1_tarski(k2_relat_1(k4_relat_1(sK6)),X0) != iProver_top
% 6.02/1.50      | v1_funct_1(k4_relat_1(sK6)) != iProver_top
% 6.02/1.50      | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
% 6.02/1.50      inference(superposition,[status(thm)],[c_12107,c_10899]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_12132,plain,
% 6.02/1.50      ( v1_funct_2(k4_relat_1(sK6),k2_relat_1(sK6),X0) = iProver_top
% 6.02/1.50      | r1_tarski(k1_relat_1(sK6),X0) != iProver_top
% 6.02/1.50      | v1_funct_1(k4_relat_1(sK6)) != iProver_top
% 6.02/1.50      | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
% 6.02/1.50      inference(light_normalisation,[status(thm)],[c_12127,c_12106]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_12156,plain,
% 6.02/1.50      ( v1_funct_2(k4_relat_1(sK6),k2_relat_1(sK6),X0) = iProver_top
% 6.02/1.50      | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
% 6.02/1.50      inference(global_propositional_subsumption,
% 6.02/1.50                [status(thm)],
% 6.02/1.50                [c_12132,c_72,c_74,c_75,c_11498,c_11501,c_11515]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_14690,plain,
% 6.02/1.50      ( v1_funct_2(k4_relat_1(sK6),sK5,X0) = iProver_top
% 6.02/1.50      | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
% 6.02/1.50      inference(demodulation,[status(thm)],[c_14576,c_12156]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(c_24462,plain,
% 6.02/1.50      ( r1_tarski(k1_relat_1(sK6),sK4) != iProver_top ),
% 6.02/1.50      inference(forward_subsumption_resolution,
% 6.02/1.50                [status(thm)],
% 6.02/1.50                [c_24287,c_14690]) ).
% 6.02/1.50  
% 6.02/1.50  cnf(contradiction,plain,
% 6.02/1.50      ( $false ),
% 6.02/1.50      inference(minisat,
% 6.02/1.50                [status(thm)],
% 6.02/1.50                [c_25004,c_24462,c_11515,c_75,c_74,c_72]) ).
% 6.02/1.50  
% 6.02/1.50  
% 6.02/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 6.02/1.50  
% 6.02/1.50  ------                               Statistics
% 6.02/1.50  
% 6.02/1.50  ------ General
% 6.02/1.50  
% 6.02/1.50  abstr_ref_over_cycles:                  0
% 6.02/1.50  abstr_ref_under_cycles:                 0
% 6.02/1.50  gc_basic_clause_elim:                   0
% 6.02/1.50  forced_gc_time:                         0
% 6.02/1.50  parsing_time:                           0.012
% 6.02/1.50  unif_index_cands_time:                  0.
% 6.02/1.50  unif_index_add_time:                    0.
% 6.02/1.50  orderings_time:                         0.
% 6.02/1.50  out_proof_time:                         0.01
% 6.02/1.50  total_time:                             0.578
% 6.02/1.50  num_of_symbols:                         65
% 6.02/1.50  num_of_terms:                           18065
% 6.02/1.50  
% 6.02/1.50  ------ Preprocessing
% 6.02/1.50  
% 6.02/1.50  num_of_splits:                          0
% 6.02/1.50  num_of_split_atoms:                     0
% 6.02/1.50  num_of_reused_defs:                     0
% 6.02/1.50  num_eq_ax_congr_red:                    69
% 6.02/1.50  num_of_sem_filtered_clauses:            1
% 6.02/1.50  num_of_subtypes:                        0
% 6.02/1.50  monotx_restored_types:                  0
% 6.02/1.50  sat_num_of_epr_types:                   0
% 6.02/1.50  sat_num_of_non_cyclic_types:            0
% 6.02/1.50  sat_guarded_non_collapsed_types:        0
% 6.02/1.50  num_pure_diseq_elim:                    0
% 6.02/1.50  simp_replaced_by:                       0
% 6.02/1.50  res_preprocessed:                       335
% 6.02/1.50  prep_upred:                             0
% 6.02/1.50  prep_unflattend:                        582
% 6.02/1.50  smt_new_axioms:                         0
% 6.02/1.50  pred_elim_cands:                        8
% 6.02/1.50  pred_elim:                              0
% 6.02/1.50  pred_elim_cl:                           0
% 6.02/1.50  pred_elim_cycles:                       10
% 6.02/1.50  merged_defs:                            0
% 6.02/1.50  merged_defs_ncl:                        0
% 6.02/1.50  bin_hyper_res:                          0
% 6.02/1.50  prep_cycles:                            4
% 6.02/1.50  pred_elim_time:                         0.143
% 6.02/1.50  splitting_time:                         0.
% 6.02/1.50  sem_filter_time:                        0.
% 6.02/1.50  monotx_time:                            0.
% 6.02/1.50  subtype_inf_time:                       0.
% 6.02/1.50  
% 6.02/1.50  ------ Problem properties
% 6.02/1.50  
% 6.02/1.50  clauses:                                70
% 6.02/1.50  conjectures:                            6
% 6.02/1.50  epr:                                    3
% 6.02/1.50  horn:                                   59
% 6.02/1.50  ground:                                 8
% 6.02/1.50  unary:                                  16
% 6.02/1.50  binary:                                 11
% 6.02/1.50  lits:                                   192
% 6.02/1.50  lits_eq:                                53
% 6.02/1.50  fd_pure:                                0
% 6.02/1.50  fd_pseudo:                              0
% 6.02/1.50  fd_cond:                                7
% 6.02/1.50  fd_pseudo_cond:                         1
% 6.02/1.50  ac_symbols:                             0
% 6.02/1.50  
% 6.02/1.50  ------ Propositional Solver
% 6.02/1.50  
% 6.02/1.50  prop_solver_calls:                      28
% 6.02/1.50  prop_fast_solver_calls:                 4219
% 6.02/1.50  smt_solver_calls:                       0
% 6.02/1.50  smt_fast_solver_calls:                  0
% 6.02/1.50  prop_num_of_clauses:                    6405
% 6.02/1.50  prop_preprocess_simplified:             20522
% 6.02/1.50  prop_fo_subsumed:                       78
% 6.02/1.50  prop_solver_time:                       0.
% 6.02/1.50  smt_solver_time:                        0.
% 6.02/1.50  smt_fast_solver_time:                   0.
% 6.02/1.50  prop_fast_solver_time:                  0.
% 6.02/1.50  prop_unsat_core_time:                   0.
% 6.02/1.50  
% 6.02/1.50  ------ QBF
% 6.02/1.50  
% 6.02/1.50  qbf_q_res:                              0
% 6.02/1.50  qbf_num_tautologies:                    0
% 6.02/1.50  qbf_prep_cycles:                        0
% 6.02/1.50  
% 6.02/1.50  ------ BMC1
% 6.02/1.50  
% 6.02/1.50  bmc1_current_bound:                     -1
% 6.02/1.50  bmc1_last_solved_bound:                 -1
% 6.02/1.50  bmc1_unsat_core_size:                   -1
% 6.02/1.50  bmc1_unsat_core_parents_size:           -1
% 6.02/1.50  bmc1_merge_next_fun:                    0
% 6.02/1.50  bmc1_unsat_core_clauses_time:           0.
% 6.02/1.50  
% 6.02/1.50  ------ Instantiation
% 6.02/1.50  
% 6.02/1.50  inst_num_of_clauses:                    1953
% 6.02/1.50  inst_num_in_passive:                    816
% 6.02/1.50  inst_num_in_active:                     836
% 6.02/1.50  inst_num_in_unprocessed:                301
% 6.02/1.50  inst_num_of_loops:                      890
% 6.02/1.50  inst_num_of_learning_restarts:          0
% 6.02/1.50  inst_num_moves_active_passive:          52
% 6.02/1.50  inst_lit_activity:                      0
% 6.02/1.50  inst_lit_activity_moves:                0
% 6.02/1.50  inst_num_tautologies:                   0
% 6.02/1.50  inst_num_prop_implied:                  0
% 6.02/1.50  inst_num_existing_simplified:           0
% 6.02/1.50  inst_num_eq_res_simplified:             0
% 6.02/1.50  inst_num_child_elim:                    0
% 6.02/1.50  inst_num_of_dismatching_blockings:      482
% 6.02/1.50  inst_num_of_non_proper_insts:           1238
% 6.02/1.50  inst_num_of_duplicates:                 0
% 6.02/1.50  inst_inst_num_from_inst_to_res:         0
% 6.02/1.50  inst_dismatching_checking_time:         0.
% 6.02/1.50  
% 6.02/1.50  ------ Resolution
% 6.02/1.50  
% 6.02/1.50  res_num_of_clauses:                     0
% 6.02/1.50  res_num_in_passive:                     0
% 6.02/1.50  res_num_in_active:                      0
% 6.02/1.50  res_num_of_loops:                       339
% 6.02/1.50  res_forward_subset_subsumed:            51
% 6.02/1.50  res_backward_subset_subsumed:           4
% 6.02/1.50  res_forward_subsumed:                   2
% 6.02/1.50  res_backward_subsumed:                  0
% 6.02/1.50  res_forward_subsumption_resolution:     10
% 6.02/1.50  res_backward_subsumption_resolution:    0
% 6.02/1.50  res_clause_to_clause_subsumption:       778
% 6.02/1.50  res_orphan_elimination:                 0
% 6.02/1.50  res_tautology_del:                      95
% 6.02/1.50  res_num_eq_res_simplified:              0
% 6.02/1.50  res_num_sel_changes:                    0
% 6.02/1.50  res_moves_from_active_to_pass:          0
% 6.02/1.50  
% 6.02/1.50  ------ Superposition
% 6.02/1.50  
% 6.02/1.50  sup_time_total:                         0.
% 6.02/1.50  sup_time_generating:                    0.
% 6.02/1.50  sup_time_sim_full:                      0.
% 6.02/1.50  sup_time_sim_immed:                     0.
% 6.02/1.50  
% 6.02/1.50  sup_num_of_clauses:                     276
% 6.02/1.50  sup_num_in_active:                      142
% 6.02/1.50  sup_num_in_passive:                     134
% 6.02/1.50  sup_num_of_loops:                       176
% 6.02/1.50  sup_fw_superposition:                   159
% 6.02/1.50  sup_bw_superposition:                   126
% 6.02/1.50  sup_immediate_simplified:               103
% 6.02/1.50  sup_given_eliminated:                   0
% 6.02/1.50  comparisons_done:                       0
% 6.02/1.50  comparisons_avoided:                    0
% 6.02/1.50  
% 6.02/1.50  ------ Simplifications
% 6.02/1.50  
% 6.02/1.50  
% 6.02/1.50  sim_fw_subset_subsumed:                 19
% 6.02/1.50  sim_bw_subset_subsumed:                 1
% 6.02/1.50  sim_fw_subsumed:                        2
% 6.02/1.50  sim_bw_subsumed:                        0
% 6.02/1.50  sim_fw_subsumption_res:                 2
% 6.02/1.50  sim_bw_subsumption_res:                 0
% 6.02/1.50  sim_tautology_del:                      7
% 6.02/1.50  sim_eq_tautology_del:                   7
% 6.02/1.50  sim_eq_res_simp:                        0
% 6.02/1.50  sim_fw_demodulated:                     18
% 6.02/1.50  sim_bw_demodulated:                     39
% 6.02/1.50  sim_light_normalised:                   77
% 6.02/1.50  sim_joinable_taut:                      0
% 6.02/1.50  sim_joinable_simp:                      0
% 6.02/1.50  sim_ac_normalised:                      0
% 6.02/1.50  sim_smt_subsumption:                    0
% 6.02/1.50  
%------------------------------------------------------------------------------
