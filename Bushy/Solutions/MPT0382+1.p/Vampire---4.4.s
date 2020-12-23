%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t64_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:26 EDT 2019

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
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
fof(f42,plain,(
    $false ),
    inference(subsumption_resolution,[],[f41,f31])).

fof(f31,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != sK2
    & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != X2
          & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( sK2 != X1
        & k3_subset_1(X0,sK2) = k3_subset_1(X0,X1)
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t64_subset_1.p',t64_subset_1)).

fof(f41,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f40,f36])).

fof(f36,plain,(
    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    inference(resolution,[],[f28,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t64_subset_1.p',involutiveness_k3_subset_1)).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK2 ),
    inference(forward_demodulation,[],[f38,f30])).

fof(f30,plain,(
    k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    inference(resolution,[],[f29,f32])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
