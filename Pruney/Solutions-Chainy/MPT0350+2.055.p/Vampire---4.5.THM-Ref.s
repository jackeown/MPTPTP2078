%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:58 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 950 expanded)
%              Number of leaves         :   32 ( 292 expanded)
%              Depth                    :   24
%              Number of atoms          :  278 (1909 expanded)
%              Number of equality atoms :  110 ( 888 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f723,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f122,f178,f182,f722])).

fof(f722,plain,
    ( ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f721])).

fof(f721,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f170,f716])).

fof(f716,plain,
    ( sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f355,f674])).

fof(f674,plain,
    ( sK0 = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f324,f673])).

fof(f673,plain,
    ( sK0 = k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f325,f316])).

fof(f316,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f315,f220])).

fof(f220,plain,
    ( sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_2 ),
    inference(superposition,[],[f218,f52])).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f218,plain,
    ( sK0 = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f217,f163])).

fof(f163,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f94,f139])).

fof(f139,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f109,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

% (1007)Refutation not found, incomplete strategy% (1007)------------------------------
% (1007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f109,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f106,f63])).

% (1007)Termination reason: Refutation not found, incomplete strategy

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

% (1007)Memory used [KB]: 10746
% (1007)Time elapsed: 0.128 s
fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

% (1007)------------------------------
% (1007)------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f106,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f104,f91])).

fof(f91,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f104,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_2
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f94,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f44,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f217,plain,
    ( sK0 = k5_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f136,f139])).

fof(f136,plain,(
    sK0 = k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f135,f86])).

fof(f86,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f54,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f82])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f70,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f74,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f75,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f76,f77])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f135,plain,(
    ! [X3] : sK0 = k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),X3)))) ),
    inference(forward_demodulation,[],[f130,f48])).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f130,plain,(
    ! [X3] : k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),X3)))) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f108,f85])).

fof(f85,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f53,f57,f83])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f108,plain,(
    ! [X0] : k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),X0)) = k5_xboole_0(k3_subset_1(sK0,sK1),X0) ),
    inference(superposition,[],[f71,f94])).

fof(f71,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f315,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f300,f52])).

fof(f300,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
    | ~ spl3_2 ),
    inference(superposition,[],[f290,f49])).

fof(f49,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f290,plain,
    ( ! [X0] : k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,X0))) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(X0,sK1))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f133,f163])).

fof(f133,plain,(
    ! [X0] : k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(X0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,X0))) ),
    inference(forward_demodulation,[],[f126,f51])).

fof(f126,plain,(
    ! [X0] : k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(X0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,X0),sK1)) ),
    inference(superposition,[],[f108,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f325,plain,
    ( k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
    | ~ spl3_2 ),
    inference(superposition,[],[f324,f52])).

fof(f324,plain,
    ( k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK0)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f323,f220])).

fof(f323,plain,
    ( k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f157,f163])).

fof(f157,plain,(
    k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(sK1,k3_subset_1(sK0,sK1)),k5_xboole_0(sK1,k3_subset_1(sK0,sK1))) ),
    inference(resolution,[],[f119,f44])).

fof(f119,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,k3_subset_1(sK0,X2),sK1) = k5_xboole_0(k3_xboole_0(sK1,k3_subset_1(sK0,X2)),k5_xboole_0(sK1,k3_subset_1(sK0,X2))) ) ),
    inference(forward_demodulation,[],[f118,f51])).

fof(f118,plain,(
    ! [X2] :
      ( k4_subset_1(sK0,k3_subset_1(sK0,X2),sK1) = k5_xboole_0(k3_xboole_0(k3_subset_1(sK0,X2),sK1),k5_xboole_0(sK1,k3_subset_1(sK0,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    inference(forward_demodulation,[],[f112,f52])).

fof(f112,plain,(
    ! [X2] :
      ( k4_subset_1(sK0,k3_subset_1(sK0,X2),sK1) = k5_xboole_0(k3_xboole_0(k3_subset_1(sK0,X2),sK1),k5_xboole_0(k3_subset_1(sK0,X2),sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f98,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK1) = k5_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(X0,sK1)) ) ),
    inference(forward_demodulation,[],[f97,f52])).

fof(f97,plain,(
    ! [X0] :
      ( k4_subset_1(sK0,X0,sK1) = k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(X0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(forward_demodulation,[],[f93,f87])).

fof(f87,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f83])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f93,plain,(
    ! [X0] :
      ( k4_subset_1(sK0,X0,sK1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f44,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f73,f83])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f355,plain,
    ( k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK0)
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f342,f220])).

fof(f342,plain,
    ( k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
    | ~ spl3_6 ),
    inference(resolution,[],[f206,f44])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,sK1)),k5_xboole_0(X0,k5_xboole_0(sK0,sK1))) )
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f205,f52])).

fof(f205,plain,
    ( ! [X0] :
        ( k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK0,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f199,f87])).

fof(f199,plain,
    ( ! [X0] :
        ( k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl3_6 ),
    inference(resolution,[],[f177,f89])).

fof(f177,plain,
    ( m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl3_6
  <=> m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f170,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f92,f163])).

fof(f92,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f45,f47])).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f45,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f182,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f44,f174])).

fof(f174,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f178,plain,
    ( ~ spl3_5
    | spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f171,f103,f176,f173])).

fof(f171,plain,
    ( m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(superposition,[],[f64,f163])).

fof(f122,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl3_1 ),
    inference(resolution,[],[f101,f46])).

fof(f46,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f101,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl3_1
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f105,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f95,f103,f100])).

fof(f95,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f44,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:13:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.53  % (986)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (983)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (990)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (1006)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (1000)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (984)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (985)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (1009)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (982)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (1014)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.57  % (989)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.57  % (995)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (1008)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.57  % (1003)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  % (997)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.57  % (999)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.59  % (987)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.53/0.60  % (1007)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.53/0.60  % (998)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.53/0.60  % (1011)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.53/0.60  % (1013)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.53/0.60  % (1001)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.53/0.61  % (1010)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.61  % (1002)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.53/0.61  % (1004)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.53/0.61  % (984)Refutation found. Thanks to Tanya!
% 1.53/0.61  % SZS status Theorem for theBenchmark
% 1.53/0.61  % SZS output start Proof for theBenchmark
% 1.53/0.61  fof(f723,plain,(
% 1.53/0.61    $false),
% 1.53/0.61    inference(avatar_sat_refutation,[],[f105,f122,f178,f182,f722])).
% 1.53/0.61  fof(f722,plain,(
% 1.53/0.61    ~spl3_2 | ~spl3_6),
% 1.53/0.61    inference(avatar_contradiction_clause,[],[f721])).
% 1.53/0.61  fof(f721,plain,(
% 1.53/0.61    $false | (~spl3_2 | ~spl3_6)),
% 1.53/0.61    inference(subsumption_resolution,[],[f170,f716])).
% 1.53/0.61  fof(f716,plain,(
% 1.53/0.61    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) | (~spl3_2 | ~spl3_6)),
% 1.53/0.61    inference(forward_demodulation,[],[f355,f674])).
% 1.53/0.61  fof(f674,plain,(
% 1.53/0.61    sK0 = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK0) | ~spl3_2),
% 1.53/0.61    inference(backward_demodulation,[],[f324,f673])).
% 1.53/0.61  fof(f673,plain,(
% 1.53/0.61    sK0 = k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) | ~spl3_2),
% 1.53/0.61    inference(forward_demodulation,[],[f325,f316])).
% 1.53/0.61  fof(f316,plain,(
% 1.53/0.61    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | ~spl3_2),
% 1.53/0.61    inference(forward_demodulation,[],[f315,f220])).
% 1.53/0.61  fof(f220,plain,(
% 1.53/0.61    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~spl3_2),
% 1.53/0.61    inference(superposition,[],[f218,f52])).
% 1.53/0.61  fof(f52,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f2])).
% 1.53/0.61  fof(f2,axiom,(
% 1.53/0.61    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.53/0.61  fof(f218,plain,(
% 1.53/0.61    sK0 = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) | ~spl3_2),
% 1.53/0.61    inference(forward_demodulation,[],[f217,f163])).
% 1.53/0.61  fof(f163,plain,(
% 1.53/0.61    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~spl3_2),
% 1.53/0.61    inference(backward_demodulation,[],[f94,f139])).
% 1.53/0.61  fof(f139,plain,(
% 1.53/0.61    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_2),
% 1.53/0.61    inference(superposition,[],[f109,f51])).
% 1.53/0.61  fof(f51,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f1])).
% 1.53/0.61  fof(f1,axiom,(
% 1.53/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.53/0.61  % (1007)Refutation not found, incomplete strategy% (1007)------------------------------
% 1.53/0.61  % (1007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.61  fof(f109,plain,(
% 1.53/0.61    sK1 = k3_xboole_0(sK1,sK0) | ~spl3_2),
% 1.53/0.61    inference(resolution,[],[f106,f63])).
% 1.53/0.61  % (1007)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.61  
% 1.53/0.61  fof(f63,plain,(
% 1.53/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.53/0.61    inference(cnf_transformation,[],[f32])).
% 1.53/0.61  % (1007)Memory used [KB]: 10746
% 1.53/0.61  % (1007)Time elapsed: 0.128 s
% 1.53/0.61  fof(f32,plain,(
% 1.53/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.53/0.61    inference(ennf_transformation,[],[f7])).
% 1.53/0.61  % (1007)------------------------------
% 1.53/0.61  % (1007)------------------------------
% 1.53/0.61  fof(f7,axiom,(
% 1.53/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.53/0.61  fof(f106,plain,(
% 1.53/0.61    r1_tarski(sK1,sK0) | ~spl3_2),
% 1.53/0.61    inference(resolution,[],[f104,f91])).
% 1.53/0.61  fof(f91,plain,(
% 1.53/0.61    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.53/0.61    inference(equality_resolution,[],[f66])).
% 1.53/0.61  fof(f66,plain,(
% 1.53/0.61    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.53/0.61    inference(cnf_transformation,[],[f43])).
% 1.53/0.61  fof(f43,plain,(
% 1.53/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.53/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 1.53/0.61  fof(f42,plain,(
% 1.53/0.61    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.53/0.61    introduced(choice_axiom,[])).
% 1.53/0.61  fof(f41,plain,(
% 1.53/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.53/0.61    inference(rectify,[],[f40])).
% 1.53/0.61  fof(f40,plain,(
% 1.53/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.53/0.61    inference(nnf_transformation,[],[f19])).
% 1.53/0.61  fof(f19,axiom,(
% 1.53/0.61    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.53/0.61  fof(f104,plain,(
% 1.53/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.53/0.61    inference(avatar_component_clause,[],[f103])).
% 1.53/0.61  fof(f103,plain,(
% 1.53/0.61    spl3_2 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.53/0.61  fof(f94,plain,(
% 1.53/0.61    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.53/0.61    inference(resolution,[],[f44,f88])).
% 1.53/0.61  fof(f88,plain,(
% 1.53/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.53/0.61    inference(definition_unfolding,[],[f65,f57])).
% 1.53/0.61  fof(f57,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.53/0.61    inference(cnf_transformation,[],[f4])).
% 1.53/0.61  fof(f4,axiom,(
% 1.53/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.53/0.61  fof(f65,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.53/0.61    inference(cnf_transformation,[],[f34])).
% 1.53/0.61  fof(f34,plain,(
% 1.53/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.61    inference(ennf_transformation,[],[f23])).
% 1.53/0.61  fof(f23,axiom,(
% 1.53/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.53/0.61  fof(f44,plain,(
% 1.53/0.61    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.53/0.61    inference(cnf_transformation,[],[f38])).
% 1.53/0.61  fof(f38,plain,(
% 1.53/0.61    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.53/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f37])).
% 1.53/0.61  fof(f37,plain,(
% 1.53/0.61    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.53/0.61    introduced(choice_axiom,[])).
% 1.53/0.61  fof(f30,plain,(
% 1.53/0.61    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.61    inference(ennf_transformation,[],[f28])).
% 1.53/0.61  fof(f28,negated_conjecture,(
% 1.53/0.61    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.53/0.61    inference(negated_conjecture,[],[f27])).
% 1.53/0.61  fof(f27,conjecture,(
% 1.53/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 1.53/0.61  fof(f217,plain,(
% 1.53/0.61    sK0 = k5_xboole_0(k3_subset_1(sK0,sK1),sK1) | ~spl3_2),
% 1.53/0.61    inference(forward_demodulation,[],[f136,f139])).
% 1.53/0.61  fof(f136,plain,(
% 1.53/0.61    sK0 = k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.53/0.61    inference(forward_demodulation,[],[f135,f86])).
% 1.53/0.61  fof(f86,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0) )),
% 1.53/0.61    inference(definition_unfolding,[],[f54,f83])).
% 1.53/0.61  fof(f83,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.53/0.61    inference(definition_unfolding,[],[f55,f82])).
% 1.53/0.61  fof(f82,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.53/0.61    inference(definition_unfolding,[],[f56,f81])).
% 1.53/0.61  fof(f81,plain,(
% 1.53/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.53/0.61    inference(definition_unfolding,[],[f70,f80])).
% 1.53/0.61  fof(f80,plain,(
% 1.53/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.53/0.61    inference(definition_unfolding,[],[f74,f79])).
% 1.53/0.61  fof(f79,plain,(
% 1.53/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.53/0.61    inference(definition_unfolding,[],[f75,f78])).
% 1.53/0.61  fof(f78,plain,(
% 1.53/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.53/0.61    inference(definition_unfolding,[],[f76,f77])).
% 1.53/0.61  fof(f77,plain,(
% 1.53/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f18])).
% 1.53/0.61  fof(f18,axiom,(
% 1.53/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.53/0.61  fof(f76,plain,(
% 1.53/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f17])).
% 1.53/0.61  fof(f17,axiom,(
% 1.53/0.61    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.53/0.61  fof(f75,plain,(
% 1.53/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f16])).
% 1.53/0.61  fof(f16,axiom,(
% 1.53/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.53/0.61  fof(f74,plain,(
% 1.53/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f15])).
% 1.53/0.61  fof(f15,axiom,(
% 1.53/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.53/0.61  fof(f70,plain,(
% 1.53/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f14])).
% 1.53/0.61  fof(f14,axiom,(
% 1.53/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.53/0.61  fof(f56,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f13])).
% 1.53/0.61  fof(f13,axiom,(
% 1.53/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.53/0.61  fof(f55,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.53/0.61    inference(cnf_transformation,[],[f20])).
% 1.53/0.61  fof(f20,axiom,(
% 1.53/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.53/0.61  fof(f54,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.53/0.61    inference(cnf_transformation,[],[f6])).
% 1.53/0.61  fof(f6,axiom,(
% 1.53/0.61    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.53/0.61  fof(f135,plain,(
% 1.53/0.61    ( ! [X3] : (sK0 = k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),X3))))) )),
% 1.53/0.61    inference(forward_demodulation,[],[f130,f48])).
% 1.53/0.61  fof(f48,plain,(
% 1.53/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.53/0.61    inference(cnf_transformation,[],[f10])).
% 1.53/0.61  fof(f10,axiom,(
% 1.53/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.53/0.61  fof(f130,plain,(
% 1.53/0.61    ( ! [X3] : (k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),X3)))) = k5_xboole_0(sK0,k1_xboole_0)) )),
% 1.53/0.61    inference(superposition,[],[f108,f85])).
% 1.53/0.61  fof(f85,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.53/0.61    inference(definition_unfolding,[],[f53,f57,f83])).
% 1.53/0.61  fof(f53,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.53/0.61    inference(cnf_transformation,[],[f9])).
% 1.53/0.61  fof(f9,axiom,(
% 1.53/0.61    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.53/0.61  fof(f108,plain,(
% 1.53/0.61    ( ! [X0] : (k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),X0)) = k5_xboole_0(k3_subset_1(sK0,sK1),X0)) )),
% 1.53/0.61    inference(superposition,[],[f71,f94])).
% 1.53/0.61  fof(f71,plain,(
% 1.53/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.53/0.61    inference(cnf_transformation,[],[f11])).
% 1.53/0.61  fof(f11,axiom,(
% 1.53/0.61    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.53/0.61  fof(f315,plain,(
% 1.53/0.61    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | ~spl3_2),
% 1.53/0.61    inference(forward_demodulation,[],[f300,f52])).
% 1.53/0.61  fof(f300,plain,(
% 1.53/0.61    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | ~spl3_2),
% 1.53/0.61    inference(superposition,[],[f290,f49])).
% 1.53/0.61  fof(f49,plain,(
% 1.53/0.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.53/0.61    inference(cnf_transformation,[],[f29])).
% 1.53/0.61  fof(f29,plain,(
% 1.53/0.61    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.53/0.61    inference(rectify,[],[f3])).
% 1.53/0.61  fof(f3,axiom,(
% 1.53/0.61    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.53/0.61  fof(f290,plain,(
% 1.53/0.61    ( ! [X0] : (k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,X0))) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(X0,sK1))) ) | ~spl3_2),
% 1.53/0.61    inference(forward_demodulation,[],[f133,f163])).
% 1.53/0.61  fof(f133,plain,(
% 1.53/0.61    ( ! [X0] : (k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(X0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,X0)))) )),
% 1.53/0.61    inference(forward_demodulation,[],[f126,f51])).
% 1.53/0.61  fof(f126,plain,(
% 1.53/0.61    ( ! [X0] : (k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(X0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,X0),sK1))) )),
% 1.53/0.61    inference(superposition,[],[f108,f72])).
% 1.53/0.61  fof(f72,plain,(
% 1.53/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f5])).
% 1.53/0.61  fof(f5,axiom,(
% 1.53/0.61    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.53/0.61  fof(f325,plain,(
% 1.53/0.61    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | ~spl3_2),
% 1.53/0.61    inference(superposition,[],[f324,f52])).
% 1.53/0.61  fof(f324,plain,(
% 1.53/0.61    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK0) | ~spl3_2),
% 1.53/0.61    inference(forward_demodulation,[],[f323,f220])).
% 1.53/0.61  fof(f323,plain,(
% 1.53/0.61    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | ~spl3_2),
% 1.53/0.61    inference(forward_demodulation,[],[f157,f163])).
% 1.53/0.61  fof(f157,plain,(
% 1.53/0.61    k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(sK1,k3_subset_1(sK0,sK1)),k5_xboole_0(sK1,k3_subset_1(sK0,sK1)))),
% 1.53/0.61    inference(resolution,[],[f119,f44])).
% 1.53/0.61  fof(f119,plain,(
% 1.53/0.61    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,k3_subset_1(sK0,X2),sK1) = k5_xboole_0(k3_xboole_0(sK1,k3_subset_1(sK0,X2)),k5_xboole_0(sK1,k3_subset_1(sK0,X2)))) )),
% 1.53/0.61    inference(forward_demodulation,[],[f118,f51])).
% 1.53/0.61  fof(f118,plain,(
% 1.53/0.61    ( ! [X2] : (k4_subset_1(sK0,k3_subset_1(sK0,X2),sK1) = k5_xboole_0(k3_xboole_0(k3_subset_1(sK0,X2),sK1),k5_xboole_0(sK1,k3_subset_1(sK0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(sK0))) )),
% 1.53/0.61    inference(forward_demodulation,[],[f112,f52])).
% 1.53/0.61  fof(f112,plain,(
% 1.53/0.61    ( ! [X2] : (k4_subset_1(sK0,k3_subset_1(sK0,X2),sK1) = k5_xboole_0(k3_xboole_0(k3_subset_1(sK0,X2),sK1),k5_xboole_0(k3_subset_1(sK0,X2),sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(sK0))) )),
% 1.53/0.61    inference(resolution,[],[f98,f64])).
% 1.53/0.61  fof(f64,plain,(
% 1.53/0.61    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.53/0.61    inference(cnf_transformation,[],[f33])).
% 1.53/0.61  fof(f33,plain,(
% 1.53/0.61    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.61    inference(ennf_transformation,[],[f24])).
% 1.53/0.61  fof(f24,axiom,(
% 1.53/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.53/0.61  fof(f98,plain,(
% 1.53/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k5_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(X0,sK1))) )),
% 1.53/0.61    inference(forward_demodulation,[],[f97,f52])).
% 1.53/0.61  fof(f97,plain,(
% 1.53/0.61    ( ! [X0] : (k4_subset_1(sK0,X0,sK1) = k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(X0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 1.53/0.61    inference(forward_demodulation,[],[f93,f87])).
% 1.53/0.61  fof(f87,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.53/0.61    inference(definition_unfolding,[],[f58,f83])).
% 1.53/0.61  fof(f58,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.53/0.61    inference(cnf_transformation,[],[f12])).
% 1.53/0.61  fof(f12,axiom,(
% 1.53/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.53/0.61  fof(f93,plain,(
% 1.53/0.61    ( ! [X0] : (k4_subset_1(sK0,X0,sK1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 1.53/0.61    inference(resolution,[],[f44,f89])).
% 1.53/0.61  fof(f89,plain,(
% 1.53/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.53/0.61    inference(definition_unfolding,[],[f73,f83])).
% 1.53/0.61  fof(f73,plain,(
% 1.53/0.61    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.53/0.61    inference(cnf_transformation,[],[f36])).
% 1.53/0.61  fof(f36,plain,(
% 1.53/0.61    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.61    inference(flattening,[],[f35])).
% 1.53/0.61  fof(f35,plain,(
% 1.53/0.61    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.53/0.61    inference(ennf_transformation,[],[f26])).
% 1.53/0.61  fof(f26,axiom,(
% 1.53/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.53/0.61  fof(f355,plain,(
% 1.53/0.61    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK0) | (~spl3_2 | ~spl3_6)),
% 1.53/0.61    inference(forward_demodulation,[],[f342,f220])).
% 1.53/0.61  fof(f342,plain,(
% 1.53/0.61    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | ~spl3_6),
% 1.53/0.61    inference(resolution,[],[f206,f44])).
% 1.53/0.61  fof(f206,plain,(
% 1.53/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,sK1)),k5_xboole_0(X0,k5_xboole_0(sK0,sK1)))) ) | ~spl3_6),
% 1.53/0.61    inference(forward_demodulation,[],[f205,f52])).
% 1.53/0.61  fof(f205,plain,(
% 1.53/0.61    ( ! [X0] : (k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK0,sK1)),k3_xboole_0(X0,k5_xboole_0(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | ~spl3_6),
% 1.53/0.61    inference(forward_demodulation,[],[f199,f87])).
% 1.53/0.61  fof(f199,plain,(
% 1.53/0.61    ( ! [X0] : (k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | ~spl3_6),
% 1.53/0.61    inference(resolution,[],[f177,f89])).
% 1.53/0.61  fof(f177,plain,(
% 1.53/0.61    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_6),
% 1.53/0.61    inference(avatar_component_clause,[],[f176])).
% 1.53/0.61  fof(f176,plain,(
% 1.53/0.61    spl3_6 <=> m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.53/0.61  fof(f170,plain,(
% 1.53/0.61    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) | ~spl3_2),
% 1.53/0.61    inference(backward_demodulation,[],[f92,f163])).
% 1.53/0.61  fof(f92,plain,(
% 1.53/0.61    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.53/0.61    inference(forward_demodulation,[],[f45,f47])).
% 1.53/0.61  fof(f47,plain,(
% 1.53/0.61    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.53/0.61    inference(cnf_transformation,[],[f22])).
% 1.53/0.61  fof(f22,axiom,(
% 1.53/0.61    ! [X0] : k2_subset_1(X0) = X0),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.53/0.61  fof(f45,plain,(
% 1.53/0.61    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.53/0.61    inference(cnf_transformation,[],[f38])).
% 1.53/0.61  fof(f182,plain,(
% 1.53/0.61    spl3_5),
% 1.53/0.61    inference(avatar_contradiction_clause,[],[f179])).
% 1.53/0.61  fof(f179,plain,(
% 1.53/0.61    $false | spl3_5),
% 1.53/0.61    inference(subsumption_resolution,[],[f44,f174])).
% 1.53/0.61  fof(f174,plain,(
% 1.53/0.61    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_5),
% 1.53/0.61    inference(avatar_component_clause,[],[f173])).
% 1.53/0.61  fof(f173,plain,(
% 1.53/0.61    spl3_5 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.53/0.61  fof(f178,plain,(
% 1.53/0.61    ~spl3_5 | spl3_6 | ~spl3_2),
% 1.53/0.61    inference(avatar_split_clause,[],[f171,f103,f176,f173])).
% 1.53/0.61  fof(f171,plain,(
% 1.53/0.61    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.53/0.61    inference(superposition,[],[f64,f163])).
% 1.53/0.61  fof(f122,plain,(
% 1.53/0.61    ~spl3_1),
% 1.53/0.61    inference(avatar_contradiction_clause,[],[f121])).
% 1.53/0.61  fof(f121,plain,(
% 1.53/0.61    $false | ~spl3_1),
% 1.53/0.61    inference(resolution,[],[f101,f46])).
% 1.53/0.61  fof(f46,plain,(
% 1.53/0.61    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.53/0.61    inference(cnf_transformation,[],[f25])).
% 1.53/0.61  fof(f25,axiom,(
% 1.53/0.61    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.53/0.61  fof(f101,plain,(
% 1.53/0.61    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_1),
% 1.53/0.61    inference(avatar_component_clause,[],[f100])).
% 1.53/0.61  fof(f100,plain,(
% 1.53/0.61    spl3_1 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.53/0.61  fof(f105,plain,(
% 1.53/0.61    spl3_1 | spl3_2),
% 1.53/0.61    inference(avatar_split_clause,[],[f95,f103,f100])).
% 1.53/0.61  fof(f95,plain,(
% 1.53/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.53/0.61    inference(resolution,[],[f44,f59])).
% 1.53/0.61  fof(f59,plain,(
% 1.53/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f39])).
% 1.53/0.61  fof(f39,plain,(
% 1.53/0.61    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.53/0.61    inference(nnf_transformation,[],[f31])).
% 1.53/0.61  fof(f31,plain,(
% 1.53/0.61    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.53/0.61    inference(ennf_transformation,[],[f21])).
% 1.53/0.61  fof(f21,axiom,(
% 1.53/0.61    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.53/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.53/0.61  % SZS output end Proof for theBenchmark
% 1.53/0.61  % (984)------------------------------
% 1.53/0.61  % (984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.61  % (984)Termination reason: Refutation
% 1.53/0.61  
% 1.53/0.61  % (984)Memory used [KB]: 11257
% 1.53/0.61  % (984)Time elapsed: 0.199 s
% 1.53/0.61  % (984)------------------------------
% 1.53/0.61  % (984)------------------------------
% 1.53/0.61  % (996)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.53/0.61  % (988)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.53/0.61  % (992)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.93/0.62  % (991)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.93/0.62  % (1012)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.93/0.62  % (981)Success in time 0.261 s
%------------------------------------------------------------------------------
