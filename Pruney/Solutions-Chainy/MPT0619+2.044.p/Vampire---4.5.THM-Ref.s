%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 (1139 expanded)
%              Number of leaves         :    9 ( 283 expanded)
%              Depth                    :   23
%              Number of atoms          :  197 (3031 expanded)
%              Number of equality atoms :  103 (1771 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (21276)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f295,plain,(
    $false ),
    inference(global_subsumption,[],[f263,f294])).

fof(f294,plain,(
    ~ r2_hidden(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f293,f225])).

fof(f225,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f86,f222])).

fof(f222,plain,(
    ! [X4] :
      ( k1_xboole_0 = k2_relat_1(sK1)
      | ~ sP3(X4,sK1) ) ),
    inference(global_subsumption,[],[f49,f159,f216])).

fof(f216,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,sK0) != X4
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
      | ~ sP3(X4,sK1) ) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,sK0) != X4
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
      | ~ sP3(X4,sK1)
      | k1_xboole_0 = k2_relat_1(sK1) ) ),
    inference(superposition,[],[f51,f177])).

fof(f177,plain,(
    ! [X5] :
      ( sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = X5
      | ~ sP3(X5,sK1)
      | k1_xboole_0 = k2_relat_1(sK1) ) ),
    inference(resolution,[],[f163,f111])).

fof(f111,plain,
    ( sP3(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),sK1)
    | k1_xboole_0 = k2_relat_1(sK1) ),
    inference(global_subsumption,[],[f19,f18,f110])).

fof(f110,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | sP3(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f109,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

% (21281)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f109,plain,
    ( r2_hidden(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1))
    | k1_xboole_0 = k2_relat_1(sK1) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X1] :
      ( k2_relat_1(sK1) != X1
      | k1_xboole_0 = X1
      | r2_hidden(sK5(X1,k1_funct_1(sK1,sK0)),X1) ) ),
    inference(superposition,[],[f49,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

% (21296)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f19,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ sP3(X1,sK1)
      | X0 = X1
      | ~ sP3(X0,sK1) ) ),
    inference(superposition,[],[f159,f159])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X1
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f34,f48])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | sK5(X0,X1) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f159,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = X0
      | ~ sP3(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = X0
      | ~ sP3(X0,sK1)
      | ~ sP3(X0,sK1) ) ),
    inference(superposition,[],[f27,f152])).

fof(f152,plain,(
    ! [X0] :
      ( sK0 = sK4(sK1,X0)
      | ~ sP3(X0,sK1) ) ),
    inference(resolution,[],[f147,f26])).

fof(f26,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f147,plain,(
    ! [X16] :
      ( ~ r2_hidden(X16,k1_relat_1(sK1))
      | sK0 = X16 ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X16] :
      ( sK0 = X16
      | sK0 = X16
      | sK0 = X16
      | sK0 = X16
      | ~ r2_hidden(X16,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f41,f69])).

fof(f69,plain,(
    ! [X0] :
      ( sP7(X0,sK0,sK0,sK0,sK0)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f60,f50])).

fof(f50,plain,(
    k1_relat_1(sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f20,f48])).

fof(f20,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X5,k3_enumset1(X0,X0,X1,X2,X3))
      | sP7(X5,X3,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP7(X5,X3,X2,X1,X0)
      | ~ r2_hidden(X5,X4)
      | k3_enumset1(X0,X0,X1,X2,X3) != X4 ) ),
    inference(definition_unfolding,[],[f43,f36])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP7(X5,X3,X2,X1,X0)
      | ~ r2_hidden(X5,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP7(X5,X3,X2,X1,X0)
      | X1 = X5
      | X2 = X5
      | X3 = X5
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X2,X0] :
      ( k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    k2_relat_1(sK1) != k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f21,f48])).

fof(f21,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f86,plain,(
    sP3(k1_funct_1(sK1,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f79,f59])).

fof(f59,plain,(
    ! [X0,X3] :
      ( sP3(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f65,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ sP7(X0,sK0,sK0,sK0,sK0)
      | r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f61,f50])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,k3_enumset1(X0,X0,X1,X2,X3))
      | ~ sP7(X5,X3,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP7(X5,X3,X2,X1,X0)
      | r2_hidden(X5,X4)
      | k3_enumset1(X0,X0,X1,X2,X3) != X4 ) ),
    inference(definition_unfolding,[],[f42,f36])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP7(X5,X3,X2,X1,X0)
      | r2_hidden(X5,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X2,X5,X3,X1] : sP7(X5,X3,X2,X1,X5) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X0 != X5
      | sP7(X5,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f293,plain,(
    ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f18,f19,f273,f57])).

fof(f273,plain,(
    ~ sP3(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f272])).

fof(f272,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ sP3(sK0,sK1) ),
    inference(backward_demodulation,[],[f248,f255])).

fof(f255,plain,(
    k1_xboole_0 = k1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f18,f225,f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f248,plain,
    ( k1_xboole_0 != k1_relat_1(sK1)
    | ~ sP3(sK0,sK1) ),
    inference(backward_demodulation,[],[f185,f225])).

fof(f185,plain,
    ( k1_relat_1(sK1) != k2_relat_1(sK1)
    | ~ sP3(sK0,sK1) ),
    inference(superposition,[],[f164,f50])).

fof(f164,plain,(
    ! [X0] :
      ( k2_relat_1(sK1) != k3_enumset1(X0,X0,X0,X0,X0)
      | ~ sP3(X0,sK1) ) ),
    inference(superposition,[],[f49,f159])).

fof(f263,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f79,f255])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:46:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (21283)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (21270)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (21274)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (21295)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (21275)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (21278)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (21284)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (21272)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (21273)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (21271)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (21294)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (21286)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (21299)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (21285)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (21291)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (21277)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (21295)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (21279)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  % (21276)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  fof(f295,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(global_subsumption,[],[f263,f294])).
% 0.22/0.53  fof(f294,plain,(
% 0.22/0.53    ~r2_hidden(sK0,k1_xboole_0)),
% 0.22/0.53    inference(forward_demodulation,[],[f293,f225])).
% 0.22/0.53  fof(f225,plain,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(sK1)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f86,f222])).
% 0.22/0.53  fof(f222,plain,(
% 0.22/0.53    ( ! [X4] : (k1_xboole_0 = k2_relat_1(sK1) | ~sP3(X4,sK1)) )),
% 0.22/0.53    inference(global_subsumption,[],[f49,f159,f216])).
% 0.22/0.53  fof(f216,plain,(
% 0.22/0.53    ( ! [X4] : (k1_funct_1(sK1,sK0) != X4 | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | ~sP3(X4,sK1)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f215])).
% 0.22/0.53  fof(f215,plain,(
% 0.22/0.53    ( ! [X4] : (k1_funct_1(sK1,sK0) != X4 | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | ~sP3(X4,sK1) | k1_xboole_0 = k2_relat_1(sK1)) )),
% 0.22/0.53    inference(superposition,[],[f51,f177])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    ( ! [X5] : (sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = X5 | ~sP3(X5,sK1) | k1_xboole_0 = k2_relat_1(sK1)) )),
% 0.22/0.53    inference(resolution,[],[f163,f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    sP3(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),sK1) | k1_xboole_0 = k2_relat_1(sK1)),
% 0.22/0.53    inference(global_subsumption,[],[f19,f18,f110])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(sK1) | ~v1_funct_1(sK1) | sP3(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),sK1) | ~v1_relat_1(sK1)),
% 0.22/0.53    inference(resolution,[],[f109,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | sP3(X2,X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP3(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  % (21281)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    r2_hidden(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1)) | k1_xboole_0 = k2_relat_1(sK1)),
% 0.22/0.53    inference(equality_resolution,[],[f102])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ( ! [X1] : (k2_relat_1(sK1) != X1 | k1_xboole_0 = X1 | r2_hidden(sK5(X1,k1_funct_1(sK1,sK0)),X1)) )),
% 0.22/0.53    inference(superposition,[],[f49,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f33,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f22,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f32,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f35,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  % (21296)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    v1_relat_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.53    inference(negated_conjecture,[],[f9])).
% 0.22/0.53  fof(f9,conjecture,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    v1_funct_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~sP3(X1,sK1) | X0 = X1 | ~sP3(X0,sK1)) )),
% 0.22/0.53    inference(superposition,[],[f159,f159])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK5(X0,X1) != X1 | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 0.22/0.53    inference(definition_unfolding,[],[f34,f48])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | sK5(X0,X1) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    ( ! [X0] : (k1_funct_1(sK1,sK0) = X0 | ~sP3(X0,sK1)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f156])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    ( ! [X0] : (k1_funct_1(sK1,sK0) = X0 | ~sP3(X0,sK1) | ~sP3(X0,sK1)) )),
% 0.22/0.53    inference(superposition,[],[f27,f152])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    ( ! [X0] : (sK0 = sK4(sK1,X0) | ~sP3(X0,sK1)) )),
% 0.22/0.54    inference(resolution,[],[f147,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X2,X0] : (r2_hidden(sK4(X0,X2),k1_relat_1(X0)) | ~sP3(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    ( ! [X16] : (~r2_hidden(X16,k1_relat_1(sK1)) | sK0 = X16) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f144])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    ( ! [X16] : (sK0 = X16 | sK0 = X16 | sK0 = X16 | sK0 = X16 | ~r2_hidden(X16,k1_relat_1(sK1))) )),
% 0.22/0.54    inference(resolution,[],[f41,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X0] : (sP7(X0,sK0,sK0,sK0,sK0) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.22/0.54    inference(superposition,[],[f60,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    k1_relat_1(sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.54    inference(definition_unfolding,[],[f20,f48])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X2,X0,X5,X3,X1] : (~r2_hidden(X5,k3_enumset1(X0,X0,X1,X2,X3)) | sP7(X5,X3,X2,X1,X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (sP7(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4) | k3_enumset1(X0,X0,X1,X2,X3) != X4) )),
% 0.22/0.54    inference(definition_unfolding,[],[f43,f36])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (sP7(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X2,X0,X5,X3,X1] : (~sP7(X5,X3,X2,X1,X0) | X1 = X5 | X2 = X5 | X3 = X5 | X0 = X5) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X2,X0] : (k1_funct_1(X0,sK4(X0,X2)) = X2 | ~sP3(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    k2_relat_1(sK1) != k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.22/0.54    inference(definition_unfolding,[],[f21,f48])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    sP3(k1_funct_1(sK1,sK0),sK1)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f79,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0,X3] : (sP3(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 0.22/0.54    inference(equality_resolution,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP3(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f65,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0] : (~sP7(X0,sK0,sK0,sK0,sK0) | r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.22/0.54    inference(superposition,[],[f61,f50])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X1,X2,X3)) | ~sP7(X5,X3,X2,X1,X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~sP7(X5,X3,X2,X1,X0) | r2_hidden(X5,X4) | k3_enumset1(X0,X0,X1,X2,X3) != X4) )),
% 0.22/0.54    inference(definition_unfolding,[],[f42,f36])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~sP7(X5,X3,X2,X1,X0) | r2_hidden(X5,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X2,X5,X3,X1] : (sP7(X5,X3,X2,X1,X5)) )),
% 0.22/0.54    inference(equality_resolution,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X2,X0,X5,X3,X1] : (X0 != X5 | sP7(X5,X3,X2,X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f293,plain,(
% 0.22/0.54    ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f18,f19,f273,f57])).
% 0.22/0.54  fof(f273,plain,(
% 0.22/0.54    ~sP3(sK0,sK1)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f272])).
% 0.22/0.54  fof(f272,plain,(
% 0.22/0.54    k1_xboole_0 != k1_xboole_0 | ~sP3(sK0,sK1)),
% 0.22/0.54    inference(backward_demodulation,[],[f248,f255])).
% 0.22/0.54  fof(f255,plain,(
% 0.22/0.54    k1_xboole_0 = k1_relat_1(sK1)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f18,f225,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.22/0.54  fof(f248,plain,(
% 0.22/0.54    k1_xboole_0 != k1_relat_1(sK1) | ~sP3(sK0,sK1)),
% 0.22/0.54    inference(backward_demodulation,[],[f185,f225])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    k1_relat_1(sK1) != k2_relat_1(sK1) | ~sP3(sK0,sK1)),
% 0.22/0.54    inference(superposition,[],[f164,f50])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    ( ! [X0] : (k2_relat_1(sK1) != k3_enumset1(X0,X0,X0,X0,X0) | ~sP3(X0,sK1)) )),
% 0.22/0.54    inference(superposition,[],[f49,f159])).
% 0.22/0.54  fof(f263,plain,(
% 0.22/0.54    r2_hidden(sK0,k1_xboole_0)),
% 0.22/0.54    inference(backward_demodulation,[],[f79,f255])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (21295)------------------------------
% 0.22/0.54  % (21295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21295)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (21295)Memory used [KB]: 6396
% 0.22/0.54  % (21295)Time elapsed: 0.115 s
% 0.22/0.54  % (21295)------------------------------
% 0.22/0.54  % (21295)------------------------------
% 0.22/0.54  % (21267)Success in time 0.17 s
%------------------------------------------------------------------------------
