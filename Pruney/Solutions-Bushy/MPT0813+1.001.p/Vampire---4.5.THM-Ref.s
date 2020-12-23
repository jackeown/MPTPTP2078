%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0813+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:41 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   21 (  35 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  98 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(subsumption_resolution,[],[f22,f20])).

fof(f20,plain,(
    ~ r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f14,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f14,plain,(
    ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & r1_tarski(sK0,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & r1_tarski(X0,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
   => ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & r1_tarski(sK0,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ( r1_tarski(X0,X3)
         => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

fof(f22,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f13,f18,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f18,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f12,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,plain,(
    r1_tarski(sK0,sK3) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
