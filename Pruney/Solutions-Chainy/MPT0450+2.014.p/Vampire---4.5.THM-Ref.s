%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:19 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 127 expanded)
%              Number of leaves         :   14 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :  211 ( 343 expanded)
%              Number of equality atoms :   64 ( 101 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f29,f51,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),X0) ) ),
    inference(resolution,[],[f82,f39])).

fof(f39,plain,(
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

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f81,f60])).

fof(f60,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK1)) ) ),
    inference(resolution,[],[f74,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f74,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
      | ~ m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f73,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f73,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
      | ~ m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f72,f29])).

fof(f72,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
      | ~ m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f71,f51])).

fof(f71,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
      | ~ m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ) ),
    inference(resolution,[],[f70,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f70,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0))
      | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
      | ~ m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f69,f33])).

fof(f69,plain,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f68,f30])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

fof(f68,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(resolution,[],[f67,f32])).

fof(f67,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) ),
    inference(resolution,[],[f52,f50])).

fof(f50,plain,(
    ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f31,f49,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f48])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:54:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (2435)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (2422)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (2420)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (2429)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.26/0.52  % (2440)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.26/0.52  % (2440)Refutation found. Thanks to Tanya!
% 1.26/0.52  % SZS status Theorem for theBenchmark
% 1.26/0.52  % SZS output start Proof for theBenchmark
% 1.26/0.52  fof(f85,plain,(
% 1.26/0.52    $false),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f29,f51,f83])).
% 1.26/0.52  fof(f83,plain,(
% 1.26/0.52    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),X0)) )),
% 1.26/0.52    inference(resolution,[],[f82,f39])).
% 1.26/0.52  fof(f39,plain,(
% 1.26/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f23])).
% 1.26/0.52  fof(f23,plain,(
% 1.26/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.26/0.52    inference(nnf_transformation,[],[f7])).
% 1.26/0.52  fof(f7,axiom,(
% 1.26/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.26/0.52  fof(f82,plain,(
% 1.26/0.52    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.26/0.52    inference(subsumption_resolution,[],[f81,f60])).
% 1.26/0.52  fof(f60,plain,(
% 1.26/0.52    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 1.26/0.52    inference(equality_resolution,[],[f59])).
% 1.26/0.52  fof(f59,plain,(
% 1.26/0.52    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 1.26/0.52    inference(equality_resolution,[],[f56])).
% 1.26/0.52  fof(f56,plain,(
% 1.26/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.26/0.52    inference(definition_unfolding,[],[f44,f48])).
% 1.26/0.52  fof(f48,plain,(
% 1.26/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.26/0.52    inference(definition_unfolding,[],[f35,f40])).
% 1.26/0.52  fof(f40,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f5])).
% 1.26/0.52  fof(f5,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.26/0.52  fof(f35,plain,(
% 1.26/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f4])).
% 1.26/0.52  fof(f4,axiom,(
% 1.26/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.26/0.52  fof(f44,plain,(
% 1.26/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.26/0.52    inference(cnf_transformation,[],[f28])).
% 1.26/0.52  fof(f28,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.26/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 1.26/0.52  fof(f27,plain,(
% 1.26/0.52    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f26,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.26/0.52    inference(rectify,[],[f25])).
% 1.26/0.52  fof(f25,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.26/0.52    inference(flattening,[],[f24])).
% 1.26/0.52  fof(f24,plain,(
% 1.26/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.26/0.52    inference(nnf_transformation,[],[f3])).
% 1.26/0.52  fof(f3,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.26/0.52  fof(f81,plain,(
% 1.26/0.52    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK1))) )),
% 1.26/0.52    inference(resolution,[],[f74,f37])).
% 1.26/0.52  fof(f37,plain,(
% 1.26/0.52    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f17])).
% 1.26/0.52  fof(f17,plain,(
% 1.26/0.52    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 1.26/0.52    inference(ennf_transformation,[],[f8])).
% 1.26/0.52  fof(f8,axiom,(
% 1.26/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.26/0.52  fof(f74,plain,(
% 1.26/0.52    ( ! [X0] : (~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | ~m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.26/0.52    inference(subsumption_resolution,[],[f73,f33])).
% 1.26/0.52  fof(f33,plain,(
% 1.26/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f16])).
% 1.26/0.52  fof(f16,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.26/0.52    inference(ennf_transformation,[],[f9])).
% 1.26/0.52  fof(f9,axiom,(
% 1.26/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.26/0.52  fof(f73,plain,(
% 1.26/0.52    ( ! [X0] : (~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | ~m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) )),
% 1.26/0.52    inference(subsumption_resolution,[],[f72,f29])).
% 1.26/0.52  fof(f72,plain,(
% 1.26/0.52    ( ! [X0] : (~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | ~m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) )),
% 1.26/0.52    inference(subsumption_resolution,[],[f71,f51])).
% 1.26/0.52  fof(f71,plain,(
% 1.26/0.52    ( ! [X0] : (~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | ~m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) )),
% 1.26/0.52    inference(resolution,[],[f70,f32])).
% 1.26/0.52  fof(f32,plain,(
% 1.26/0.52    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f15])).
% 1.26/0.52  fof(f15,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.26/0.52    inference(flattening,[],[f14])).
% 1.26/0.52  fof(f14,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.26/0.52    inference(ennf_transformation,[],[f10])).
% 1.26/0.52  fof(f10,axiom,(
% 1.26/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 1.26/0.52  fof(f70,plain,(
% 1.26/0.52    ( ! [X0] : (~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | ~m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.26/0.52    inference(resolution,[],[f69,f33])).
% 1.26/0.52  fof(f69,plain,(
% 1.26/0.52    ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0))),
% 1.26/0.52    inference(subsumption_resolution,[],[f68,f30])).
% 1.26/0.52  fof(f30,plain,(
% 1.26/0.52    v1_relat_1(sK1)),
% 1.26/0.52    inference(cnf_transformation,[],[f22])).
% 1.26/0.52  fof(f22,plain,(
% 1.26/0.52    (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.26/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f21,f20])).
% 1.26/0.52  fof(f20,plain,(
% 1.26/0.52    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f21,plain,(
% 1.26/0.52    ? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f13,plain,(
% 1.26/0.52    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.26/0.52    inference(ennf_transformation,[],[f12])).
% 1.26/0.52  fof(f12,negated_conjecture,(
% 1.26/0.52    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.26/0.52    inference(negated_conjecture,[],[f11])).
% 1.26/0.52  fof(f11,conjecture,(
% 1.26/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).
% 1.26/0.52  fof(f68,plain,(
% 1.26/0.52    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 1.26/0.52    inference(resolution,[],[f67,f32])).
% 1.26/0.52  fof(f67,plain,(
% 1.26/0.52    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1)) | ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0))),
% 1.26/0.52    inference(resolution,[],[f52,f50])).
% 1.26/0.52  fof(f50,plain,(
% 1.26/0.52    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1))))),
% 1.26/0.52    inference(definition_unfolding,[],[f31,f49,f49])).
% 1.26/0.52  fof(f49,plain,(
% 1.26/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.26/0.52    inference(definition_unfolding,[],[f36,f48])).
% 1.26/0.52  fof(f36,plain,(
% 1.26/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f6])).
% 1.26/0.52  fof(f6,axiom,(
% 1.26/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.26/0.52  fof(f31,plain,(
% 1.26/0.52    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 1.26/0.52    inference(cnf_transformation,[],[f22])).
% 1.26/0.52  fof(f52,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.26/0.52    inference(definition_unfolding,[],[f41,f49])).
% 1.26/0.52  fof(f41,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f19])).
% 1.26/0.52  fof(f19,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.26/0.52    inference(flattening,[],[f18])).
% 1.26/0.52  fof(f18,plain,(
% 1.26/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.26/0.52    inference(ennf_transformation,[],[f2])).
% 1.26/0.52  fof(f2,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.26/0.52  fof(f51,plain,(
% 1.26/0.52    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 1.26/0.52    inference(definition_unfolding,[],[f34,f49])).
% 1.26/0.52  fof(f34,plain,(
% 1.26/0.52    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f1])).
% 1.26/0.52  fof(f1,axiom,(
% 1.26/0.52    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.26/0.52  fof(f29,plain,(
% 1.26/0.52    v1_relat_1(sK0)),
% 1.26/0.52    inference(cnf_transformation,[],[f22])).
% 1.26/0.52  % SZS output end Proof for theBenchmark
% 1.26/0.52  % (2440)------------------------------
% 1.26/0.52  % (2440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (2440)Termination reason: Refutation
% 1.26/0.52  
% 1.26/0.52  % (2440)Memory used [KB]: 6268
% 1.26/0.52  % (2440)Time elapsed: 0.079 s
% 1.26/0.52  % (2440)------------------------------
% 1.26/0.52  % (2440)------------------------------
% 1.26/0.52  % (2417)Success in time 0.16 s
%------------------------------------------------------------------------------
