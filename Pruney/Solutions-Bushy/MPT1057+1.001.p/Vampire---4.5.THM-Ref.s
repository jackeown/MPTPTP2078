%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1057+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:11 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   32 (  54 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 150 expanded)
%              Number of equality atoms :   24 (  51 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f45,plain,(
    $false ),
    inference(subsumption_resolution,[],[f44,f20])).

fof(f20,plain,(
    k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(sK2,sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(X2,X1) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(sK0,X2) != k9_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(X2,X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2,X1] :
        ( k9_relat_1(sK0,X2) != k9_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(X2,X1) )
   => ( k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(X2,X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X2,X1)
           => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X2,X1)
           => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X2,X1)
         => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_2)).

fof(f44,plain,(
    k9_relat_1(sK0,sK2) = k9_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(superposition,[],[f43,f31])).

fof(f31,plain,(
    sK2 = k9_relat_1(k6_relat_1(sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f26,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f19,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f19,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0,X1] : k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(forward_demodulation,[],[f37,f27])).

fof(f27,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0) ),
    inference(unit_resulting_resolution,[],[f18,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] : k9_relat_1(k5_relat_1(k6_relat_1(X0),sK0),X1) = k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X1)) ),
    inference(unit_resulting_resolution,[],[f21,f18,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

%------------------------------------------------------------------------------
