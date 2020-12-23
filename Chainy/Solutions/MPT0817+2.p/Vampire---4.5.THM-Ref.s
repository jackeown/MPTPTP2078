%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0817+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:49 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
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
fof(f6765,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6764,f6702])).

fof(f6702,plain,(
    v1_relat_1(sK26) ),
    inference(resolution,[],[f3334,f4912])).

fof(f4912,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2248])).

fof(f2248,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f3334,plain,(
    m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK23,sK25))) ),
    inference(cnf_transformation,[],[f2507])).

fof(f2507,plain,
    ( ~ m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK24,sK25)))
    & r1_tarski(k1_relat_1(sK26),sK24)
    & m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK23,sK25))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23,sK24,sK25,sK26])],[f1249,f2506])).

fof(f2506,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & r1_tarski(k1_relat_1(X3),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK24,sK25)))
      & r1_tarski(k1_relat_1(sK26),sK24)
      & m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK23,sK25))) ) ),
    introduced(choice_axiom,[])).

fof(f1249,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(k1_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f1248])).

fof(f1248,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(k1_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f1216])).

fof(f1216,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ( r1_tarski(k1_relat_1(X3),X1)
         => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f1215])).

fof(f1215,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f6764,plain,(
    ~ v1_relat_1(sK26) ),
    inference(subsumption_resolution,[],[f6763,f6704])).

fof(f6704,plain,(
    v5_relat_1(sK26,sK25) ),
    inference(resolution,[],[f3334,f4914])).

fof(f4914,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f2249])).

fof(f2249,plain,(
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

fof(f6763,plain,
    ( ~ v5_relat_1(sK26,sK25)
    | ~ v1_relat_1(sK26) ),
    inference(resolution,[],[f6762,f4213])).

fof(f4213,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2868])).

fof(f2868,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1733])).

fof(f1733,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f652])).

fof(f652,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f6762,plain,(
    ~ r1_tarski(k2_relat_1(sK26),sK25) ),
    inference(subsumption_resolution,[],[f6761,f6702])).

fof(f6761,plain,
    ( ~ r1_tarski(k2_relat_1(sK26),sK25)
    | ~ v1_relat_1(sK26) ),
    inference(subsumption_resolution,[],[f6758,f3335])).

fof(f3335,plain,(
    r1_tarski(k1_relat_1(sK26),sK24) ),
    inference(cnf_transformation,[],[f2507])).

fof(f6758,plain,
    ( ~ r1_tarski(k2_relat_1(sK26),sK25)
    | ~ r1_tarski(k1_relat_1(sK26),sK24)
    | ~ v1_relat_1(sK26) ),
    inference(resolution,[],[f3336,f4844])).

fof(f4844,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2186])).

fof(f2186,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2185])).

fof(f2185,plain,(
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

fof(f3336,plain,(
    ~ m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(sK24,sK25))) ),
    inference(cnf_transformation,[],[f2507])).
%------------------------------------------------------------------------------
