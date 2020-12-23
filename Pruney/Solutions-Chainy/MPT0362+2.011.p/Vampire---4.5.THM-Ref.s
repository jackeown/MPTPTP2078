%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 140 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  163 ( 270 expanded)
%              Number of equality atoms :   42 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f477,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f270,f273,f476])).

fof(f476,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f475])).

fof(f475,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f470,f62])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f470,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl3_2 ),
    inference(resolution,[],[f421,f269])).

fof(f269,plain,
    ( ~ r1_tarski(k9_subset_1(sK0,sK1,sK2),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl3_2
  <=> r1_tarski(k9_subset_1(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f421,plain,(
    ! [X4,X3] :
      ( r1_tarski(k9_subset_1(sK0,X3,sK2),X4)
      | ~ r1_tarski(X3,X4) ) ),
    inference(subsumption_resolution,[],[f407,f172])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X2,k3_tarski(k2_enumset1(X0,X0,X0,X2))),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f127,f120])).

fof(f120,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f65,f117])).

fof(f117,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f116,f36])).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f116,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f59,f58])).

fof(f58,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f37,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f59,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k2_enumset1(X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f38,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f55])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f38,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f49,f36])).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X2,k3_tarski(k2_enumset1(X0,X0,X0,X2))))),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f60,f49])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X2),k3_tarski(k2_enumset1(X0,X0,X0,X2)))),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f41,f56])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f407,plain,(
    ! [X4,X3] :
      ( r1_tarski(k9_subset_1(sK0,X3,sK2),X4)
      | ~ r1_tarski(k5_xboole_0(sK2,k3_tarski(k2_enumset1(X3,X3,X3,sK2))),X4)
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f53,f286])).

fof(f286,plain,(
    ! [X1] : k9_subset_1(sK0,X1,sK2) = k5_xboole_0(X1,k5_xboole_0(sK2,k3_tarski(k2_enumset1(X1,X1,X1,sK2)))) ),
    inference(resolution,[],[f279,f34])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f28,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

fof(f279,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) ) ),
    inference(forward_demodulation,[],[f61,f49])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f273,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f271,f34])).

fof(f271,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl3_1 ),
    inference(resolution,[],[f265,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f265,plain,
    ( ~ m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl3_1
  <=> m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f270,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f261,f267,f263])).

fof(f261,plain,
    ( ~ r1_tarski(k9_subset_1(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f258,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f258,plain,
    ( ~ r1_tarski(k9_subset_1(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (23191)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (23182)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (23174)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (23179)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (23170)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (23175)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (23174)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f477,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f270,f273,f476])).
% 0.21/0.53  fof(f476,plain,(
% 0.21/0.53    spl3_2),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f475])).
% 0.21/0.53  fof(f475,plain,(
% 0.21/0.53    $false | spl3_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f470,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f470,plain,(
% 0.21/0.53    ~r1_tarski(sK1,sK1) | spl3_2),
% 0.21/0.53    inference(resolution,[],[f421,f269])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    ~r1_tarski(k9_subset_1(sK0,sK1,sK2),sK1) | spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f267])).
% 0.21/0.53  fof(f267,plain,(
% 0.21/0.53    spl3_2 <=> r1_tarski(k9_subset_1(sK0,sK1,sK2),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f421,plain,(
% 0.21/0.53    ( ! [X4,X3] : (r1_tarski(k9_subset_1(sK0,X3,sK2),X4) | ~r1_tarski(X3,X4)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f407,f172])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X2,k3_tarski(k2_enumset1(X0,X0,X0,X2))),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f127,f120])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.21/0.53    inference(backward_demodulation,[],[f65,f117])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.53    inference(forward_demodulation,[],[f116,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 0.21/0.53    inference(forward_demodulation,[],[f59,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f37,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f39,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f40,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.53    inference(rectify,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k2_enumset1(X0,X0,X0,X0))) = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f38,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f42,f55])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.53    inference(rectify,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.53    inference(superposition,[],[f49,f36])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X2,k3_tarski(k2_enumset1(X0,X0,X0,X2))))),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f60,f49])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X2),k3_tarski(k2_enumset1(X0,X0,X0,X2)))),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f50,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f41,f56])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).
% 0.21/0.53  fof(f407,plain,(
% 0.21/0.53    ( ! [X4,X3] : (r1_tarski(k9_subset_1(sK0,X3,sK2),X4) | ~r1_tarski(k5_xboole_0(sK2,k3_tarski(k2_enumset1(X3,X3,X3,sK2))),X4) | ~r1_tarski(X3,X4)) )),
% 0.21/0.53    inference(superposition,[],[f53,f286])).
% 0.21/0.53  fof(f286,plain,(
% 0.21/0.53    ( ! [X1] : (k9_subset_1(sK0,X1,sK2) = k5_xboole_0(X1,k5_xboole_0(sK2,k3_tarski(k2_enumset1(X1,X1,X1,sK2))))) )),
% 0.21/0.53    inference(resolution,[],[f279,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    (~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f28,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ? [X2] : (~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f16])).
% 0.21/0.53  fof(f16,conjecture,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).
% 0.21/0.53  fof(f279,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k2_enumset1(X1,X1,X1,X2))))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f61,f49])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k2_enumset1(X1,X1,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f52,f56])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).
% 0.21/0.53  fof(f273,plain,(
% 0.21/0.53    spl3_1),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f272])).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    $false | spl3_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f271,f34])).
% 0.21/0.53  fof(f271,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl3_1),
% 0.21/0.53    inference(resolution,[],[f265,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    ~m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) | spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f263])).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    spl3_1 <=> m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    ~spl3_1 | ~spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f261,f267,f263])).
% 0.21/0.53  fof(f261,plain,(
% 0.21/0.53    ~r1_tarski(k9_subset_1(sK0,sK1,sK2),sK1) | ~m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f258,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f258,plain,(
% 0.21/0.53    ~r1_tarski(k9_subset_1(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(k9_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(resolution,[],[f43,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (23174)------------------------------
% 0.21/0.53  % (23174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23174)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (23174)Memory used [KB]: 11001
% 0.21/0.53  % (23174)Time elapsed: 0.080 s
% 0.21/0.53  % (23174)------------------------------
% 0.21/0.53  % (23174)------------------------------
% 0.21/0.53  % (23168)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (23167)Success in time 0.177 s
%------------------------------------------------------------------------------
