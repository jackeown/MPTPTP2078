%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0827+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:50 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   40 (  79 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  101 ( 263 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3983,plain,(
    $false ),
    inference(global_subsumption,[],[f3808,f3810,f3982,f3924])).

fof(f3924,plain,(
    v1_relat_1(sK37) ),
    inference(resolution,[],[f2365,f2483])).

fof(f2483,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1333])).

fof(f1333,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f2365,plain,(
    m1_subset_1(sK37,k1_zfmisc_1(k2_zfmisc_1(sK34,sK35))) ),
    inference(cnf_transformation,[],[f1956])).

fof(f1956,plain,
    ( ( ~ r1_tarski(sK36,k2_relset_1(sK34,sK35,sK37))
      | ~ r1_tarski(sK36,k1_relset_1(sK34,sK35,sK37)) )
    & r1_tarski(k6_relat_1(sK36),sK37)
    & m1_subset_1(sK37,k1_zfmisc_1(k2_zfmisc_1(sK34,sK35))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK34,sK35,sK36,sK37])],[f1249,f1955])).

fof(f1955,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
          | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
        & r1_tarski(k6_relat_1(X2),X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r1_tarski(sK36,k2_relset_1(sK34,sK35,sK37))
        | ~ r1_tarski(sK36,k1_relset_1(sK34,sK35,sK37)) )
      & r1_tarski(k6_relat_1(sK36),sK37)
      & m1_subset_1(sK37,k1_zfmisc_1(k2_zfmisc_1(sK34,sK35))) ) ),
    introduced(choice_axiom,[])).

fof(f1249,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f1248])).

fof(f1248,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1237])).

fof(f1237,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X2),X3)
         => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
            & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f1236])).

fof(f1236,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

fof(f3982,plain,
    ( ~ r1_tarski(sK36,k1_relat_1(sK37))
    | ~ r1_tarski(sK36,k2_relat_1(sK37)) ),
    inference(backward_demodulation,[],[f3977,f3919])).

fof(f3919,plain,(
    k1_relset_1(sK34,sK35,sK37) = k1_relat_1(sK37) ),
    inference(resolution,[],[f2365,f2377])).

fof(f2377,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1255])).

fof(f1255,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1220])).

fof(f1220,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f3977,plain,
    ( ~ r1_tarski(sK36,k2_relat_1(sK37))
    | ~ r1_tarski(sK36,k1_relset_1(sK34,sK35,sK37)) ),
    inference(backward_demodulation,[],[f2367,f3914])).

fof(f3914,plain,(
    k2_relset_1(sK34,sK35,sK37) = k2_relat_1(sK37) ),
    inference(resolution,[],[f2365,f2372])).

fof(f2372,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1252])).

fof(f1252,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1221])).

fof(f1221,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f2367,plain,
    ( ~ r1_tarski(sK36,k2_relset_1(sK34,sK35,sK37))
    | ~ r1_tarski(sK36,k1_relset_1(sK34,sK35,sK37)) ),
    inference(cnf_transformation,[],[f1956])).

fof(f3810,plain,
    ( r1_tarski(sK36,k2_relat_1(sK37))
    | ~ v1_relat_1(sK37) ),
    inference(forward_demodulation,[],[f3809,f2429])).

fof(f2429,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f863,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f3809,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK36)),k2_relat_1(sK37))
    | ~ v1_relat_1(sK37) ),
    inference(subsumption_resolution,[],[f3720,f2436])).

fof(f2436,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f668])).

fof(f668,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f3720,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK36)),k2_relat_1(sK37))
    | ~ v1_relat_1(sK37)
    | ~ v1_relat_1(k6_relat_1(sK36)) ),
    inference(resolution,[],[f2366,f2632])).

fof(f2632,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1393])).

fof(f1393,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1392])).

fof(f1392,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f829])).

fof(f829,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f2366,plain,(
    r1_tarski(k6_relat_1(sK36),sK37) ),
    inference(cnf_transformation,[],[f1956])).

fof(f3808,plain,
    ( r1_tarski(sK36,k1_relat_1(sK37))
    | ~ v1_relat_1(sK37) ),
    inference(forward_demodulation,[],[f3807,f2428])).

fof(f2428,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f3807,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK36)),k1_relat_1(sK37))
    | ~ v1_relat_1(sK37) ),
    inference(subsumption_resolution,[],[f3719,f2436])).

fof(f3719,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK36)),k1_relat_1(sK37))
    | ~ v1_relat_1(sK37)
    | ~ v1_relat_1(k6_relat_1(sK36)) ),
    inference(resolution,[],[f2366,f2631])).

fof(f2631,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1393])).
%------------------------------------------------------------------------------
