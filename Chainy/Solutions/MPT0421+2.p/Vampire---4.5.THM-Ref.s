%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0421+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  43 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 ( 157 expanded)
%              Number of equality atoms :   27 (  84 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f758,plain,(
    $false ),
    inference(subsumption_resolution,[],[f757,f682])).

fof(f682,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f648])).

fof(f648,plain,
    ( sK1 != sK2
    & k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f616,f647,f646])).

fof(f646,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( sK1 != X2
          & k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f647,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( sK1 != sK2
      & k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f616,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f615])).

fof(f615,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f608])).

fof(f608,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f607])).

fof(f607,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_setfam_1)).

fof(f757,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f756,f753])).

fof(f753,plain,(
    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(resolution,[],[f695,f679])).

fof(f679,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f648])).

fof(f695,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f625])).

fof(f625,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f564])).

fof(f564,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f756,plain,(
    sK2 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f754,f681])).

fof(f681,plain,(
    k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f648])).

fof(f754,plain,(
    sK2 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK2)) ),
    inference(resolution,[],[f695,f680])).

fof(f680,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f648])).
%------------------------------------------------------------------------------
