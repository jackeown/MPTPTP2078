%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 322 expanded)
%              Number of leaves         :   22 (  92 expanded)
%              Depth                    :   25
%              Number of atoms          :  292 ( 760 expanded)
%              Number of equality atoms :  131 ( 422 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f540,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f383,f539])).

fof(f539,plain,(
    spl3_15 ),
    inference(avatar_contradiction_clause,[],[f538])).

fof(f538,plain,
    ( $false
    | spl3_15 ),
    inference(subsumption_resolution,[],[f537,f77])).

fof(f77,plain,(
    k2_relat_1(sK1) != k5_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f45,f76])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
      & k1_tarski(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f537,plain,
    ( k2_relat_1(sK1) = k5_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
    | spl3_15 ),
    inference(subsumption_resolution,[],[f531,f234])).

fof(f234,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl3_15
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f531,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | k2_relat_1(sK1) = k5_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
    | spl3_15 ),
    inference(trivial_inequality_removal,[],[f530])).

fof(f530,plain,
    ( k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0)
    | k1_xboole_0 = k2_relat_1(sK1)
    | k2_relat_1(sK1) = k5_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
    | spl3_15 ),
    inference(superposition,[],[f81,f479])).

fof(f479,plain,
    ( k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))
    | spl3_15 ),
    inference(trivial_inequality_removal,[],[f478])).

fof(f478,plain,
    ( k2_relat_1(sK1) != k2_relat_1(sK1)
    | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))
    | spl3_15 ),
    inference(superposition,[],[f77,f453])).

fof(f453,plain,
    ( ! [X1] :
        ( k2_relat_1(sK1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1)
        | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X1) )
    | spl3_15 ),
    inference(subsumption_resolution,[],[f452,f234])).

fof(f452,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X1)
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ) ),
    inference(resolution,[],[f299,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f61,f76])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f299,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK0) = X0 ) ),
    inference(subsumption_resolution,[],[f298,f42])).

fof(f42,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f298,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK0) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f295,f43])).

fof(f43,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f295,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK0) = X0
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f291,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f291,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK0,X0),sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f279,f42])).

fof(f279,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | r2_hidden(k4_tarski(sK0,X0),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f65,f276])).

fof(f276,plain,(
    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f170,f270])).

fof(f270,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(superposition,[],[f264,f110])).

fof(f110,plain,(
    ! [X0] : k2_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k9_relat_1(sK1,X0) ),
    inference(forward_demodulation,[],[f109,f51])).

fof(f51,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f109,plain,(
    ! [X0] : k2_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k9_relat_1(sK1,k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f106,f48])).

fof(f48,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f106,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,sK1)) = k9_relat_1(sK1,k2_relat_1(X0)) ) ),
    inference(resolution,[],[f55,f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f264,plain,(
    k2_relat_1(sK1) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)) ),
    inference(resolution,[],[f259,f42])).

fof(f259,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0)) ) ),
    inference(resolution,[],[f158,f83])).

% (18032)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k2_relat_1(X1) = k2_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f151,f48])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k2_relat_1(X1) = k2_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f56,f51])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f170,plain,(
    k11_relat_1(sK1,sK0) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(superposition,[],[f168,f78])).

fof(f78,plain,(
    k1_relat_1(sK1) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f44,f76])).

fof(f44,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f168,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
    inference(resolution,[],[f80,f42])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f54,f76])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f62,f76])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f383,plain,(
    ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f371,f46])).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f371,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f87,f367])).

fof(f367,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f366,f42])).

fof(f366,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f361,f83])).

fof(f361,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_15 ),
    inference(duplicate_literal_removal,[],[f358])).

fof(f358,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_15 ),
    inference(superposition,[],[f92,f233])).

fof(f233,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f232])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(extensionality_resolution,[],[f60,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f87,plain,(
    ~ v1_xboole_0(k1_relat_1(sK1)) ),
    inference(superposition,[],[f79,f78])).

fof(f79,plain,(
    ! [X0] : ~ v1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f47,f76])).

fof(f47,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:20:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.46  % (18027)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.50  % (18033)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (18036)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (18031)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.50  % (18050)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (18044)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (18048)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.51  % (18044)Refutation not found, incomplete strategy% (18044)------------------------------
% 0.20/0.51  % (18044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (18044)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (18044)Memory used [KB]: 10618
% 0.20/0.51  % (18044)Time elapsed: 0.119 s
% 0.20/0.51  % (18044)------------------------------
% 0.20/0.51  % (18044)------------------------------
% 0.20/0.51  % (18046)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (18033)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (18042)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (18040)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (18034)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (18028)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (18029)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (18051)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (18037)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f540,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f383,f539])).
% 0.20/0.52  fof(f539,plain,(
% 0.20/0.52    spl3_15),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f538])).
% 0.20/0.52  fof(f538,plain,(
% 0.20/0.52    $false | spl3_15),
% 0.20/0.52    inference(subsumption_resolution,[],[f537,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    k2_relat_1(sK1) != k5_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.20/0.52    inference(definition_unfolding,[],[f45,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f49,f75])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f57,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f63,f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f69,f72])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f70,f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.52    inference(negated_conjecture,[],[f19])).
% 0.20/0.52  fof(f19,conjecture,(
% 0.20/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.20/0.52  fof(f537,plain,(
% 0.20/0.52    k2_relat_1(sK1) = k5_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | spl3_15),
% 0.20/0.52    inference(subsumption_resolution,[],[f531,f234])).
% 0.20/0.52  fof(f234,plain,(
% 0.20/0.52    k1_xboole_0 != k2_relat_1(sK1) | spl3_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f232])).
% 0.20/0.52  fof(f232,plain,(
% 0.20/0.52    spl3_15 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.52  fof(f531,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k5_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | spl3_15),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f530])).
% 0.20/0.52  fof(f530,plain,(
% 0.20/0.52    k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0) | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k5_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | spl3_15),
% 0.20/0.52    inference(superposition,[],[f81,f479])).
% 0.20/0.52  fof(f479,plain,(
% 0.20/0.52    k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) | spl3_15),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f478])).
% 0.20/0.52  fof(f478,plain,(
% 0.20/0.52    k2_relat_1(sK1) != k2_relat_1(sK1) | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) | spl3_15),
% 0.20/0.52    inference(superposition,[],[f77,f453])).
% 0.20/0.52  fof(f453,plain,(
% 0.20/0.52    ( ! [X1] : (k2_relat_1(sK1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1) | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X1)) ) | spl3_15),
% 0.20/0.52    inference(subsumption_resolution,[],[f452,f234])).
% 0.20/0.52  fof(f452,plain,(
% 0.20/0.52    ( ! [X1] : (k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X1) | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) )),
% 0.20/0.52    inference(resolution,[],[f299,f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 0.20/0.52    inference(definition_unfolding,[],[f61,f76])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.20/0.52  fof(f299,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,sK0) = X0) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f298,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    v1_relat_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f298,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,sK0) = X0 | ~v1_relat_1(sK1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f295,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    v1_funct_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f295,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,sK0) = X0 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.20/0.52    inference(resolution,[],[f291,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(flattening,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(nnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(flattening,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.52  fof(f291,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(k4_tarski(sK0,X0),sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f279,f42])).
% 0.20/0.52  fof(f279,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(k4_tarski(sK0,X0),sK1) | ~v1_relat_1(sK1)) )),
% 0.20/0.52    inference(superposition,[],[f65,f276])).
% 0.20/0.52  fof(f276,plain,(
% 0.20/0.52    k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 0.20/0.52    inference(backward_demodulation,[],[f170,f270])).
% 0.20/0.52  fof(f270,plain,(
% 0.20/0.52    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 0.20/0.52    inference(superposition,[],[f264,f110])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    ( ! [X0] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k9_relat_1(sK1,X0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f109,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,axiom,(
% 0.20/0.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    ( ! [X0] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k9_relat_1(sK1,k2_relat_1(k6_relat_1(X0)))) )),
% 0.20/0.52    inference(resolution,[],[f106,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,sK1)) = k9_relat_1(sK1,k2_relat_1(X0))) )),
% 0.20/0.52    inference(resolution,[],[f55,f42])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.20/0.52  fof(f264,plain,(
% 0.20/0.52    k2_relat_1(sK1) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1))),
% 0.20/0.52    inference(resolution,[],[f259,f42])).
% 0.20/0.52  fof(f259,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0))) )),
% 0.20/0.52    inference(resolution,[],[f158,f83])).
% 0.20/0.52  % (18032)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(flattening,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k2_relat_1(X1) = k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f151,f48])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k2_relat_1(X1) = k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(superposition,[],[f56,f51])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.20/0.52  fof(f170,plain,(
% 0.20/0.52    k11_relat_1(sK1,sK0) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 0.20/0.52    inference(superposition,[],[f168,f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    k1_relat_1(sK1) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.52    inference(definition_unfolding,[],[f44,f76])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f168,plain,(
% 0.20/0.52    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) )),
% 0.20/0.52    inference(resolution,[],[f80,f42])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f54,f76])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(nnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 0.20/0.52    inference(definition_unfolding,[],[f62,f76])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f383,plain,(
% 0.20/0.52    ~spl3_15),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f382])).
% 0.20/0.52  fof(f382,plain,(
% 0.20/0.52    $false | ~spl3_15),
% 0.20/0.52    inference(subsumption_resolution,[],[f371,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.52  fof(f371,plain,(
% 0.20/0.52    ~v1_xboole_0(k1_xboole_0) | ~spl3_15),
% 0.20/0.52    inference(backward_demodulation,[],[f87,f367])).
% 0.20/0.52  fof(f367,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relat_1(sK1) | ~spl3_15),
% 0.20/0.52    inference(subsumption_resolution,[],[f366,f42])).
% 0.20/0.52  fof(f366,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relat_1(sK1) | ~v1_relat_1(sK1) | ~spl3_15),
% 0.20/0.52    inference(subsumption_resolution,[],[f361,f83])).
% 0.20/0.52  fof(f361,plain,(
% 0.20/0.52    ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK1) | ~v1_relat_1(sK1) | ~spl3_15),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f358])).
% 0.20/0.52  fof(f358,plain,(
% 0.20/0.52    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK1) | ~v1_relat_1(sK1) | ~spl3_15),
% 0.20/0.52    inference(superposition,[],[f92,f233])).
% 0.20/0.52  fof(f233,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(sK1) | ~spl3_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f232])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(extensionality_resolution,[],[f60,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ~v1_xboole_0(k1_relat_1(sK1))),
% 0.20/0.52    inference(superposition,[],[f79,f78])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f47,f76])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (18033)------------------------------
% 0.20/0.52  % (18033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18033)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (18033)Memory used [KB]: 11001
% 0.20/0.52  % (18033)Time elapsed: 0.103 s
% 0.20/0.52  % (18033)------------------------------
% 0.20/0.52  % (18033)------------------------------
% 0.20/0.53  % (18052)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (18024)Success in time 0.172 s
%------------------------------------------------------------------------------
