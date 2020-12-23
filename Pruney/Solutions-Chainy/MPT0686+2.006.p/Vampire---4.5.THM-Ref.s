%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 142 expanded)
%              Number of leaves         :   10 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  165 ( 511 expanded)
%              Number of equality atoms :   24 (  53 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f414,plain,(
    $false ),
    inference(global_subsumption,[],[f405,f413])).

fof(f413,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f393,f40])).

fof(f40,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f33,f27])).

fof(f27,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    & r1_xboole_0(sK1,sK2)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
            & r1_xboole_0(X1,X2) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( ~ r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2,X1] :
        ( ~ r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2))
        & r1_xboole_0(X1,X2) )
   => ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
      & r1_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_xboole_0(X1,X2)
           => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_xboole_0(X1,X2)
         => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_funct_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f393,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f41,f384])).

fof(f384,plain,(
    ! [X0,X1] : k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) ),
    inference(global_subsumption,[],[f25,f383])).

fof(f383,plain,(
    ! [X0,X1] :
      ( k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f39,f26])).

fof(f26,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    k1_xboole_0 != k3_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f34,f28])).

fof(f28,plain,(
    ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f405,plain,(
    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f385,f72])).

fof(f72,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[],[f69,f33])).

fof(f69,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f68,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f68,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f50,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k3_xboole_0(X0,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f49,f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(factoring,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f385,plain,(
    ! [X2] : k1_xboole_0 = k10_relat_1(sK0,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f384,f106])).

fof(f106,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k10_relat_1(sK0,k1_xboole_0),X0) ),
    inference(resolution,[],[f97,f25])).

fof(f97,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k1_xboole_0 = k3_xboole_0(k10_relat_1(X3,k1_xboole_0),X4) ) ),
    inference(resolution,[],[f93,f33])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k10_relat_1(X0,k1_xboole_0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f92,f30])).

fof(f92,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X11,k10_relat_1(X12,k1_xboole_0))
      | ~ v1_relat_1(X12) ) ),
    inference(resolution,[],[f37,f68])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
            & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
        & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:54:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (5860)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (5866)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.42  % (5861)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (5865)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.43  % (5858)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.43  % (5860)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f414,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(global_subsumption,[],[f405,f413])).
% 0.21/0.43  fof(f413,plain,(
% 0.21/0.43    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)),
% 0.21/0.43    inference(forward_demodulation,[],[f393,f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.21/0.43    inference(resolution,[],[f33,f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    r1_xboole_0(sK1,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    (~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) & r1_xboole_0(sK1,sK2)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16,f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (~r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ? [X2,X1] : (~r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2)) & r1_xboole_0(X1,X2)) => (~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) & r1_xboole_0(sK1,sK2))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.43    inference(flattening,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,negated_conjecture,(
% 0.21/0.43    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 0.21/0.43    inference(negated_conjecture,[],[f6])).
% 0.21/0.43  fof(f6,conjecture,(
% 0.21/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_funct_1)).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(nnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.43  fof(f393,plain,(
% 0.21/0.43    k1_xboole_0 != k10_relat_1(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.43    inference(superposition,[],[f41,f384])).
% 0.21/0.43  fof(f384,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) )),
% 0.21/0.43    inference(global_subsumption,[],[f25,f383])).
% 0.21/0.43  fof(f383,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) | ~v1_relat_1(sK0)) )),
% 0.21/0.43    inference(resolution,[],[f39,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    v1_funct_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(flattening,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    v1_relat_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    k1_xboole_0 != k3_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.21/0.43    inference(resolution,[],[f34,f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f405,plain,(
% 0.21/0.43    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)),
% 0.21/0.43    inference(forward_demodulation,[],[f385,f72])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) )),
% 0.21/0.43    inference(resolution,[],[f69,f33])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.43    inference(resolution,[],[f68,f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(rectify,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f67])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(superposition,[],[f50,f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 != k3_xboole_0(X0,X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.43    inference(resolution,[],[f49,f34])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(X1,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(factoring,[],[f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f385,plain,(
% 0.21/0.43    ( ! [X2] : (k1_xboole_0 = k10_relat_1(sK0,k3_xboole_0(k1_xboole_0,X2))) )),
% 0.21/0.43    inference(superposition,[],[f384,f106])).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k10_relat_1(sK0,k1_xboole_0),X0)) )),
% 0.21/0.43    inference(resolution,[],[f97,f25])).
% 0.21/0.43  fof(f97,plain,(
% 0.21/0.43    ( ! [X4,X3] : (~v1_relat_1(X3) | k1_xboole_0 = k3_xboole_0(k10_relat_1(X3,k1_xboole_0),X4)) )),
% 0.21/0.43    inference(resolution,[],[f93,f33])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(k10_relat_1(X0,k1_xboole_0),X1) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(resolution,[],[f92,f30])).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    ( ! [X12,X11] : (~r2_hidden(X11,k10_relat_1(X12,k1_xboole_0)) | ~v1_relat_1(X12)) )),
% 0.21/0.43    inference(resolution,[],[f37,f68])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(rectify,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(nnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (5860)------------------------------
% 0.21/0.43  % (5860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (5860)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (5860)Memory used [KB]: 6524
% 0.21/0.43  % (5860)Time elapsed: 0.016 s
% 0.21/0.43  % (5860)------------------------------
% 0.21/0.43  % (5860)------------------------------
% 0.21/0.44  % (5855)Success in time 0.074 s
%------------------------------------------------------------------------------
