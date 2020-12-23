%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 133 expanded)
%              Number of leaves         :   13 (  42 expanded)
%              Depth                    :   22
%              Number of atoms          :  198 ( 401 expanded)
%              Number of equality atoms :   14 (  55 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(resolution,[],[f214,f26])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(f214,plain,(
    ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f204,f27])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f204,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f202,f28])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f202,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f175,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f170,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f170,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),X0)
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f169,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f169,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),k1_zfmisc_1(X0))
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f158,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f158,plain,
    ( ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f154,f47])).

fof(f154,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),k1_setfam_1(k1_enumset1(sK1,sK1,X0)))
      | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f141,f45])).

fof(f141,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f134,f47])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),k1_setfam_1(k1_enumset1(X0,X0,sK2)))
      | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
      | ~ v1_relat_1(sK0)
      | ~ r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f112,f46])).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f41,f41])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f112,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),k1_setfam_1(k1_enumset1(sK2,sK2,X0)))
      | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
      | ~ v1_relat_1(sK0)
      | ~ r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f111,f45])).

fof(f111,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK1)
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | ~ r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK2)
    | ~ r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) ),
    inference(resolution,[],[f67,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(f67,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | ~ r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK2) ),
    inference(resolution,[],[f37,f59])).

fof(f59,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f44,f43])).

fof(f43,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    inference(definition_unfolding,[],[f29,f42,f42])).

fof(f29,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 11:47:53 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.51  % (22895)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (22901)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (22917)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (22895)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (22890)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (22900)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f225,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(resolution,[],[f214,f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    v1_relat_1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ((~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f21,f20,f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f10])).
% 0.21/0.54  fof(f10,conjecture,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).
% 0.21/0.54  fof(f214,plain,(
% 0.21/0.54    ~v1_relat_1(sK0)),
% 0.21/0.54    inference(resolution,[],[f204,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    v1_relat_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f204,plain,(
% 0.21/0.54    ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.54    inference(resolution,[],[f202,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    v1_relat_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f202,plain,(
% 0.21/0.54    ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f197])).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    ~v1_relat_1(sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | ~v1_relat_1(sK0)),
% 0.21/0.54    inference(resolution,[],[f175,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_relat_1(sK1) | ~v1_relat_1(X0) | ~v1_relat_1(sK2) | ~v1_relat_1(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f170,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f31,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f40,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),X0) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 0.21/0.54    inference(resolution,[],[f169,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),k1_zfmisc_1(X0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(resolution,[],[f158,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | ~v1_relat_1(sK0)),
% 0.21/0.54    inference(resolution,[],[f154,f47])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),k1_setfam_1(k1_enumset1(sK1,sK1,X0))) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | ~v1_relat_1(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f141,f45])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ~r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK1) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f134,f47])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),k1_setfam_1(k1_enumset1(X0,X0,sK2))) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~v1_relat_1(sK0) | ~r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2)) )),
% 0.21/0.54    inference(superposition,[],[f112,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f39,f41,f41])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),k1_setfam_1(k1_enumset1(sK2,sK2,X0))) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~v1_relat_1(sK0) | ~r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2)) )),
% 0.21/0.54    inference(resolution,[],[f111,f45])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ~r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~v1_relat_1(sK0) | ~r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK1) | ~v1_relat_1(sK1)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f108])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ~v1_relat_1(sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK2) | ~r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK1) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),
% 0.21/0.54    inference(resolution,[],[f67,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK2)),
% 0.21/0.54    inference(resolution,[],[f37,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK1))),
% 0.21/0.54    inference(resolution,[],[f44,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 0.21/0.54    inference(definition_unfolding,[],[f29,f42,f42])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f30,f42])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (22895)------------------------------
% 0.21/0.54  % (22895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22895)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (22895)Memory used [KB]: 1918
% 0.21/0.54  % (22895)Time elapsed: 0.103 s
% 0.21/0.54  % (22895)------------------------------
% 0.21/0.54  % (22895)------------------------------
% 0.21/0.54  % (22889)Success in time 0.181 s
%------------------------------------------------------------------------------
