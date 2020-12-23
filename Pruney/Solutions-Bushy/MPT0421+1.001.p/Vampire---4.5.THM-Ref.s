%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0421+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
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
fof(f19,plain,(
    $false ),
    inference(global_subsumption,[],[f13,f18])).

fof(f18,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f17,f15])).

fof(f15,plain,(
    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f10,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f10,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( sK1 != sK2
    & k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8,f7])).

fof(f7,plain,
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

fof(f8,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( sK1 != sK2
      & k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_setfam_1)).

fof(f17,plain,(
    sK2 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f16,f12])).

fof(f12,plain,(
    k7_setfam_1(sK0,sK1) = k7_setfam_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,plain,(
    sK2 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f11,f14])).

fof(f11,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
