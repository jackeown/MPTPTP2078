%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0817+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:53 EST 2020

% Result     : Theorem 51.28s
% Output     : CNFRefutation 51.28s
% Verified   : 
% Statistics : Number of formulae       :   36 (  56 expanded)
%              Number of clauses        :   13 (  14 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 160 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1211,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2455,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1211])).

fof(f5427,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2455])).

fof(f652,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1687,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f652])).

fof(f2891,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1687])).

fof(f4382,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2891])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2454,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f5425,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2454])).

fof(f1215,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1216,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ( r1_tarski(k1_relat_1(X3),X1)
         => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f1215])).

fof(f2460,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(k1_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f1216])).

fof(f2461,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(k1_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f2460])).

fof(f3329,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & r1_tarski(k1_relat_1(X3),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK321,sK322)))
      & r1_tarski(k1_relat_1(sK323),sK321)
      & m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK320,sK322))) ) ),
    introduced(choice_axiom,[])).

fof(f3330,plain,
    ( ~ m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK321,sK322)))
    & r1_tarski(k1_relat_1(sK323),sK321)
    & m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK320,sK322))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK320,sK321,sK322,sK323])],[f2461,f3329])).

fof(f5432,plain,(
    m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK320,sK322))) ),
    inference(cnf_transformation,[],[f3330])).

fof(f1214,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2458,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1214])).

fof(f2459,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2458])).

fof(f5431,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2459])).

fof(f5434,plain,(
    ~ m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK321,sK322))) ),
    inference(cnf_transformation,[],[f3330])).

fof(f5433,plain,(
    r1_tarski(k1_relat_1(sK323),sK321) ),
    inference(cnf_transformation,[],[f3330])).

cnf(c_2078,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f5427])).

cnf(c_129035,plain,
    ( v5_relat_1(sK323,sK322)
    | ~ m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(X0,sK322))) ),
    inference(instantiation,[status(thm)],[c_2078])).

cnf(c_195427,plain,
    ( v5_relat_1(sK323,sK322)
    | ~ m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK320,sK322))) ),
    inference(instantiation,[status(thm)],[c_129035])).

cnf(c_1036,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4382])).

cnf(c_94727,plain,
    ( ~ v5_relat_1(sK323,sK322)
    | r1_tarski(k2_relat_1(sK323),sK322)
    | ~ v1_relat_1(sK323) ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_2077,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5425])).

cnf(c_2086,negated_conjecture,
    ( m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK320,sK322))) ),
    inference(cnf_transformation,[],[f5432])).

cnf(c_91424,plain,
    ( v1_relat_1(sK323) ),
    inference(resolution,[status(thm)],[c_2077,c_2086])).

cnf(c_2083,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5431])).

cnf(c_80958,plain,
    ( m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK321,sK322)))
    | ~ r1_tarski(k1_relat_1(sK323),sK321)
    | ~ r1_tarski(k2_relat_1(sK323),sK322)
    | ~ v1_relat_1(sK323) ),
    inference(instantiation,[status(thm)],[c_2083])).

cnf(c_2084,negated_conjecture,
    ( ~ m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK321,sK322))) ),
    inference(cnf_transformation,[],[f5434])).

cnf(c_2085,negated_conjecture,
    ( r1_tarski(k1_relat_1(sK323),sK321) ),
    inference(cnf_transformation,[],[f5433])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_195427,c_94727,c_91424,c_80958,c_2084,c_2085,c_2086])).

%------------------------------------------------------------------------------
