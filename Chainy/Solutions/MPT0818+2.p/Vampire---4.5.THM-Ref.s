%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0818+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:49 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   31 (  61 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 173 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6774,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6773,f6710])).

fof(f6710,plain,(
    v1_relat_1(sK26) ),
    inference(resolution,[],[f3337,f4915])).

fof(f4915,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2249])).

fof(f2249,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f3337,plain,(
    m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK25,sK23))) ),
    inference(cnf_transformation,[],[f2510])).

fof(f2510,plain,
    ( ~ m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK25,sK24)))
    & r1_tarski(k2_relat_1(sK26),sK24)
    & m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK25,sK23))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23,sK24,sK25,sK26])],[f1250,f2509])).

fof(f2509,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & r1_tarski(k2_relat_1(X3),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ~ m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK25,sK24)))
      & r1_tarski(k2_relat_1(sK26),sK24)
      & m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK25,sK23))) ) ),
    introduced(choice_axiom,[])).

fof(f1250,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & r1_tarski(k2_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f1249])).

fof(f1249,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & r1_tarski(k2_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f1217])).

fof(f1217,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_tarski(k2_relat_1(X3),X1)
         => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    inference(negated_conjecture,[],[f1216])).

fof(f1216,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(f6773,plain,(
    ~ v1_relat_1(sK26) ),
    inference(subsumption_resolution,[],[f6772,f6711])).

fof(f6711,plain,(
    v4_relat_1(sK26,sK25) ),
    inference(resolution,[],[f3337,f4916])).

fof(f4916,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f2250])).

fof(f2250,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1211])).

fof(f1211,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f6772,plain,
    ( ~ v4_relat_1(sK26,sK25)
    | ~ v1_relat_1(sK26) ),
    inference(resolution,[],[f6771,f4214])).

fof(f4214,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2870])).

fof(f2870,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1733])).

fof(f1733,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f651])).

fof(f651,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f6771,plain,(
    ~ r1_tarski(k1_relat_1(sK26),sK25) ),
    inference(subsumption_resolution,[],[f6770,f6710])).

fof(f6770,plain,
    ( ~ r1_tarski(k1_relat_1(sK26),sK25)
    | ~ v1_relat_1(sK26) ),
    inference(subsumption_resolution,[],[f6767,f3338])).

fof(f3338,plain,(
    r1_tarski(k2_relat_1(sK26),sK24) ),
    inference(cnf_transformation,[],[f2510])).

fof(f6767,plain,
    ( ~ r1_tarski(k2_relat_1(sK26),sK24)
    | ~ r1_tarski(k1_relat_1(sK26),sK25)
    | ~ v1_relat_1(sK26) ),
    inference(resolution,[],[f3339,f4847])).

fof(f4847,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2187])).

fof(f2187,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2186])).

fof(f2186,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1214])).

fof(f1214,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f3339,plain,(
    ~ m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK25,sK24))) ),
    inference(cnf_transformation,[],[f2510])).
%------------------------------------------------------------------------------
