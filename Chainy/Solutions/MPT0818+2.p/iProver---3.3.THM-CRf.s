%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0818+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:54 EST 2020

% Result     : Theorem 55.12s
% Output     : CNFRefutation 55.12s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2456,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1211])).

fof(f5429,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2456])).

fof(f651,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1687,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f651])).

fof(f2893,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1687])).

fof(f4383,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2893])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2455,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f5428,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2455])).

fof(f1216,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1217,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_tarski(k2_relat_1(X3),X1)
         => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    inference(negated_conjecture,[],[f1216])).

fof(f2463,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & r1_tarski(k2_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f1217])).

fof(f2464,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & r1_tarski(k2_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f2463])).

fof(f3332,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & r1_tarski(k2_relat_1(X3),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ~ m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK322,sK321)))
      & r1_tarski(k2_relat_1(sK323),sK321)
      & m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK322,sK320))) ) ),
    introduced(choice_axiom,[])).

fof(f3333,plain,
    ( ~ m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK322,sK321)))
    & r1_tarski(k2_relat_1(sK323),sK321)
    & m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK322,sK320))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK320,sK321,sK322,sK323])],[f2464,f3332])).

fof(f5436,plain,(
    m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK322,sK320))) ),
    inference(cnf_transformation,[],[f3333])).

fof(f1214,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2459,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1214])).

fof(f2460,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2459])).

fof(f5434,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2460])).

fof(f5438,plain,(
    ~ m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK322,sK321))) ),
    inference(cnf_transformation,[],[f3333])).

fof(f5437,plain,(
    r1_tarski(k2_relat_1(sK323),sK321) ),
    inference(cnf_transformation,[],[f3333])).

cnf(c_2079,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f5429])).

cnf(c_129143,plain,
    ( v4_relat_1(sK323,sK322)
    | ~ m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK322,X0))) ),
    inference(instantiation,[status(thm)],[c_2079])).

cnf(c_193505,plain,
    ( v4_relat_1(sK323,sK322)
    | ~ m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK322,sK320))) ),
    inference(instantiation,[status(thm)],[c_129143])).

cnf(c_1034,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4383])).

cnf(c_94691,plain,
    ( ~ v4_relat_1(sK323,sK322)
    | r1_tarski(k1_relat_1(sK323),sK322)
    | ~ v1_relat_1(sK323) ),
    inference(instantiation,[status(thm)],[c_1034])).

cnf(c_2077,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5428])).

cnf(c_2087,negated_conjecture,
    ( m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK322,sK320))) ),
    inference(cnf_transformation,[],[f5436])).

cnf(c_92494,plain,
    ( v1_relat_1(sK323) ),
    inference(resolution,[status(thm)],[c_2077,c_2087])).

cnf(c_2083,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5434])).

cnf(c_80931,plain,
    ( m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK322,sK321)))
    | ~ r1_tarski(k1_relat_1(sK323),sK322)
    | ~ r1_tarski(k2_relat_1(sK323),sK321)
    | ~ v1_relat_1(sK323) ),
    inference(instantiation,[status(thm)],[c_2083])).

cnf(c_2085,negated_conjecture,
    ( ~ m1_subset_1(sK323,k1_zfmisc_1(k2_zfmisc_1(sK322,sK321))) ),
    inference(cnf_transformation,[],[f5438])).

cnf(c_2086,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK323),sK321) ),
    inference(cnf_transformation,[],[f5437])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_193505,c_94691,c_92494,c_80931,c_2085,c_2086,c_2087])).

%------------------------------------------------------------------------------
