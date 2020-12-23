%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:57 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 173 expanded)
%              Number of leaves         :   21 (  53 expanded)
%              Depth                    :   20
%              Number of atoms          :  226 ( 366 expanded)
%              Number of equality atoms :   89 ( 188 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f116,f131,f148,f165])).

fof(f165,plain,
    ( ~ spl1_5
    | ~ spl1_7
    | spl1_1 ),
    inference(avatar_split_clause,[],[f164,f60,f110,f102])).

fof(f102,plain,
    ( spl1_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f110,plain,
    ( spl1_7
  <=> r1_tarski(k1_xboole_0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f60,plain,
    ( spl1_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f164,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f163,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f163,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f162,f58])).

fof(f58,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f162,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))))
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f160,f34])).

fof(f34,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f160,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) ),
    inference(superposition,[],[f117,f35])).

fof(f35,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f117,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(sK0))
      | ~ v1_relat_1(X0)
      | k5_relat_1(X0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,sK0))))) ) ),
    inference(resolution,[],[f79,f31])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(X0,X1) = k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1)))))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) = k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1)))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f72,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f72,plain,(
    ! [X2,X1] :
      ( k5_relat_1(X1,X2) = k1_setfam_1(k4_enumset1(k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(k5_relat_1(X1,X2)))))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f56,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ) ),
    inference(definition_unfolding,[],[f39,f54])).

fof(f39,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f148,plain,
    ( spl1_2
    | ~ spl1_5 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl1_2
    | ~ spl1_5 ),
    inference(trivial_inequality_removal,[],[f143])).

fof(f143,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_2
    | ~ spl1_5 ),
    inference(superposition,[],[f66,f138])).

fof(f138,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_5 ),
    inference(resolution,[],[f132,f31])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) )
    | ~ spl1_5 ),
    inference(resolution,[],[f127,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f127,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X1))
        | k1_xboole_0 = k5_relat_1(X1,k1_xboole_0)
        | ~ v1_relat_1(X1) )
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f126,f34])).

fof(f126,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k5_relat_1(X1,k1_xboole_0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X1)) )
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f125,f55])).

fof(f125,plain,
    ( ! [X1] :
        ( k5_relat_1(X1,k1_xboole_0) = k1_setfam_1(k4_enumset1(k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k1_xboole_0))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X1)) )
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f124,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f124,plain,
    ( ! [X1] :
        ( k5_relat_1(X1,k1_xboole_0) = k1_setfam_1(k4_enumset1(k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,k1_xboole_0)),k1_xboole_0)))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X1)) )
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f121,f35])).

fof(f121,plain,
    ( ! [X1] :
        ( k5_relat_1(X1,k1_xboole_0) = k1_setfam_1(k4_enumset1(k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,k1_xboole_0)),k2_relat_1(k1_xboole_0))))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X1)) )
    | ~ spl1_5 ),
    inference(resolution,[],[f103,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(X0,X1) = k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) = k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f72,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f103,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f66,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl1_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f131,plain,(
    spl1_7 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl1_7 ),
    inference(resolution,[],[f112,f36])).

fof(f112,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | spl1_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f116,plain,(
    spl1_5 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl1_5 ),
    inference(resolution,[],[f114,f33])).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f114,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_5 ),
    inference(resolution,[],[f104,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f104,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f67,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f32,f64,f60])).

fof(f32,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.50  % (28037)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.50  % (28032)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.51  % (28040)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.51  % (28040)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f166,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(avatar_sat_refutation,[],[f67,f116,f131,f148,f165])).
% 0.19/0.51  fof(f165,plain,(
% 0.19/0.51    ~spl1_5 | ~spl1_7 | spl1_1),
% 0.19/0.51    inference(avatar_split_clause,[],[f164,f60,f110,f102])).
% 0.19/0.51  fof(f102,plain,(
% 0.19/0.51    spl1_5 <=> v1_relat_1(k1_xboole_0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.19/0.51  fof(f110,plain,(
% 0.19/0.51    spl1_7 <=> r1_tarski(k1_xboole_0,k1_relat_1(sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.19/0.51  fof(f60,plain,(
% 0.19/0.51    spl1_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.19/0.51  fof(f164,plain,(
% 0.19/0.51    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~r1_tarski(k1_xboole_0,k1_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0)),
% 0.19/0.51    inference(forward_demodulation,[],[f163,f55])).
% 0.19/0.51  fof(f55,plain,(
% 0.19/0.51    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 0.19/0.51    inference(definition_unfolding,[],[f37,f54])).
% 0.19/0.51  fof(f54,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 0.19/0.51    inference(definition_unfolding,[],[f42,f53])).
% 0.19/0.51  fof(f53,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f43,f52])).
% 0.19/0.51  fof(f52,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f48,f51])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f49,f50])).
% 0.19/0.51  fof(f50,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.51  fof(f49,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.51  fof(f48,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.51  fof(f43,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.51  fof(f42,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,axiom,(
% 0.19/0.51    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.19/0.51  fof(f163,plain,(
% 0.19/0.51    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)) | ~r1_tarski(k1_xboole_0,k1_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0)),
% 0.19/0.51    inference(forward_demodulation,[],[f162,f58])).
% 0.19/0.51  fof(f58,plain,(
% 0.19/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.19/0.51    inference(equality_resolution,[],[f46])).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.51    inference(flattening,[],[f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.51    inference(nnf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.51  fof(f162,plain,(
% 0.19/0.51    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) | ~r1_tarski(k1_xboole_0,k1_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0)),
% 0.19/0.51    inference(forward_demodulation,[],[f160,f34])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,axiom,(
% 0.19/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.19/0.51  fof(f160,plain,(
% 0.19/0.51    ~r1_tarski(k1_xboole_0,k1_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0) | k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))))),
% 0.19/0.51    inference(superposition,[],[f117,f35])).
% 0.19/0.51  fof(f35,plain,(
% 0.19/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f117,plain,(
% 0.19/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(sK0)) | ~v1_relat_1(X0) | k5_relat_1(X0,sK0) = k1_setfam_1(k4_enumset1(k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,sK0)))))) )),
% 0.19/0.51    inference(resolution,[],[f79,f31])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    v1_relat_1(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f28])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f27])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f17])).
% 0.19/0.51  fof(f17,negated_conjecture,(
% 0.19/0.51    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.19/0.51    inference(negated_conjecture,[],[f16])).
% 0.19/0.51  fof(f16,conjecture,(
% 0.19/0.51    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.19/0.51  fof(f79,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(X0,X1) = k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1))))) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) )),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f76])).
% 0.19/0.51  fof(f76,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1))))) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(superposition,[],[f72,f41])).
% 0.19/0.51  fof(f41,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(flattening,[],[f23])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f13])).
% 0.19/0.51  fof(f13,axiom,(
% 0.19/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.19/0.51  fof(f72,plain,(
% 0.19/0.51    ( ! [X2,X1] : (k5_relat_1(X1,X2) = k1_setfam_1(k4_enumset1(k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k5_relat_1(X1,X2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(k5_relat_1(X1,X2))))) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.19/0.51    inference(resolution,[],[f56,f44])).
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f26])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(flattening,[],[f25])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,axiom,(
% 0.19/0.51    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.19/0.51  fof(f56,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) )),
% 0.19/0.51    inference(definition_unfolding,[],[f39,f54])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f12])).
% 0.19/0.51  fof(f12,axiom,(
% 0.19/0.51    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 0.19/0.51  fof(f148,plain,(
% 0.19/0.51    spl1_2 | ~spl1_5),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f147])).
% 0.19/0.51  fof(f147,plain,(
% 0.19/0.51    $false | (spl1_2 | ~spl1_5)),
% 0.19/0.51    inference(trivial_inequality_removal,[],[f143])).
% 0.19/0.51  fof(f143,plain,(
% 0.19/0.51    k1_xboole_0 != k1_xboole_0 | (spl1_2 | ~spl1_5)),
% 0.19/0.51    inference(superposition,[],[f66,f138])).
% 0.19/0.51  fof(f138,plain,(
% 0.19/0.51    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl1_5),
% 0.19/0.51    inference(resolution,[],[f132,f31])).
% 0.19/0.51  fof(f132,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)) ) | ~spl1_5),
% 0.19/0.51    inference(resolution,[],[f127,f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.19/0.51  fof(f127,plain,(
% 0.19/0.51    ( ! [X1] : (~r1_tarski(k1_xboole_0,k2_relat_1(X1)) | k1_xboole_0 = k5_relat_1(X1,k1_xboole_0) | ~v1_relat_1(X1)) ) | ~spl1_5),
% 0.19/0.51    inference(forward_demodulation,[],[f126,f34])).
% 0.19/0.51  fof(f126,plain,(
% 0.19/0.51    ( ! [X1] : (k1_xboole_0 = k5_relat_1(X1,k1_xboole_0) | ~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X1))) ) | ~spl1_5),
% 0.19/0.51    inference(forward_demodulation,[],[f125,f55])).
% 0.19/0.51  fof(f125,plain,(
% 0.19/0.51    ( ! [X1] : (k5_relat_1(X1,k1_xboole_0) = k1_setfam_1(k4_enumset1(k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k1_xboole_0)) | ~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X1))) ) | ~spl1_5),
% 0.19/0.51    inference(forward_demodulation,[],[f124,f57])).
% 0.19/0.51  fof(f57,plain,(
% 0.19/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.51    inference(equality_resolution,[],[f47])).
% 0.19/0.51  fof(f47,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.19/0.51    inference(cnf_transformation,[],[f30])).
% 0.19/0.51  fof(f124,plain,(
% 0.19/0.51    ( ! [X1] : (k5_relat_1(X1,k1_xboole_0) = k1_setfam_1(k4_enumset1(k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,k1_xboole_0)),k1_xboole_0))) | ~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X1))) ) | ~spl1_5),
% 0.19/0.51    inference(forward_demodulation,[],[f121,f35])).
% 0.19/0.51  fof(f121,plain,(
% 0.19/0.51    ( ! [X1] : (k5_relat_1(X1,k1_xboole_0) = k1_setfam_1(k4_enumset1(k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k5_relat_1(X1,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,k1_xboole_0)),k2_relat_1(k1_xboole_0)))) | ~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(X1))) ) | ~spl1_5),
% 0.19/0.51    inference(resolution,[],[f103,f78])).
% 0.19/0.51  fof(f78,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(X0,X1) = k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)))) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0))) )),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f77])).
% 0.19/0.51  fof(f77,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)))) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 0.19/0.51    inference(superposition,[],[f72,f40])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(flattening,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f14])).
% 0.19/0.51  fof(f14,axiom,(
% 0.19/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.19/0.51  fof(f103,plain,(
% 0.19/0.51    v1_relat_1(k1_xboole_0) | ~spl1_5),
% 0.19/0.51    inference(avatar_component_clause,[],[f102])).
% 0.19/0.51  fof(f66,plain,(
% 0.19/0.51    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f64])).
% 0.19/0.51  fof(f64,plain,(
% 0.19/0.51    spl1_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.19/0.51  fof(f131,plain,(
% 0.19/0.51    spl1_7),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f130])).
% 0.19/0.51  fof(f130,plain,(
% 0.19/0.51    $false | spl1_7),
% 0.19/0.51    inference(resolution,[],[f112,f36])).
% 0.19/0.51  fof(f112,plain,(
% 0.19/0.51    ~r1_tarski(k1_xboole_0,k1_relat_1(sK0)) | spl1_7),
% 0.19/0.51    inference(avatar_component_clause,[],[f110])).
% 0.19/0.51  fof(f116,plain,(
% 0.19/0.51    spl1_5),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f115])).
% 0.19/0.51  fof(f115,plain,(
% 0.19/0.51    $false | spl1_5),
% 0.19/0.51    inference(resolution,[],[f114,f33])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    v1_xboole_0(k1_xboole_0)),
% 0.19/0.51    inference(cnf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    v1_xboole_0(k1_xboole_0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.51  fof(f114,plain,(
% 0.19/0.51    ~v1_xboole_0(k1_xboole_0) | spl1_5),
% 0.19/0.51    inference(resolution,[],[f104,f38])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,axiom,(
% 0.19/0.51    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.19/0.51  fof(f104,plain,(
% 0.19/0.51    ~v1_relat_1(k1_xboole_0) | spl1_5),
% 0.19/0.51    inference(avatar_component_clause,[],[f102])).
% 0.19/0.51  fof(f67,plain,(
% 0.19/0.51    ~spl1_1 | ~spl1_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f32,f64,f60])).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f28])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (28040)------------------------------
% 0.19/0.51  % (28040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (28040)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (28040)Memory used [KB]: 6268
% 0.19/0.51  % (28040)Time elapsed: 0.111 s
% 0.19/0.51  % (28040)------------------------------
% 0.19/0.51  % (28040)------------------------------
% 0.19/0.51  % (28039)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.51  % (28041)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.51  % (28027)Success in time 0.159 s
%------------------------------------------------------------------------------
