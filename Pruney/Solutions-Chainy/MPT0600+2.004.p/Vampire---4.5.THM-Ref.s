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
% DateTime   : Thu Dec  3 12:51:06 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 410 expanded)
%              Number of leaves         :    8 (  94 expanded)
%              Depth                    :   21
%              Number of atoms          :  213 (1884 expanded)
%              Number of equality atoms :   39 ( 219 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(resolution,[],[f124,f39])).

fof(f39,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f124,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(resolution,[],[f114,f109])).

fof(f109,plain,(
    ~ r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f26,f108])).

fof(f108,plain,(
    r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(global_subsumption,[],[f25,f107])).

fof(f107,plain,
    ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f103,f43])).

fof(f43,plain,(
    ! [X0] : k11_relat_1(sK2,X0) = k9_relat_1(sK2,k1_tarski(X0)) ),
    inference(resolution,[],[f27,f24])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
      | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
      | r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
        | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
        | r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r2_hidden(X1,k11_relat_1(X2,X0))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r2_hidden(X1,k11_relat_1(X2,X0))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r2_hidden(X1,k11_relat_1(X2,X0)) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f103,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,k9_relat_1(sK2,k1_tarski(sK0))) ),
    inference(superposition,[],[f58,f99])).

fof(f99,plain,(
    sK0 = sK4(sK1,k1_tarski(sK0),sK2) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,
    ( sK0 = sK4(sK1,k1_tarski(sK0),sK2)
    | sK0 = sK4(sK1,k1_tarski(sK0),sK2) ),
    inference(resolution,[],[f95,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k11_relat_1(sK2,X1))
      | sK4(X0,k1_tarski(X1),sK2) = X1 ) ),
    inference(resolution,[],[f51,f40])).

fof(f40,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1,k1_tarski(X0),sK2),k1_tarski(X0))
      | ~ r2_hidden(X1,k11_relat_1(sK2,X0)) ) ),
    inference(superposition,[],[f50,f43])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK2,X1))
      | r2_hidden(sK4(X0,X1,sK2),X1) ) ),
    inference(resolution,[],[f36,f24])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK4(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
            & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f95,plain,
    ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | sK0 = sK4(sK1,k1_tarski(sK0),sK2) ),
    inference(resolution,[],[f93,f40])).

fof(f93,plain,
    ( r2_hidden(sK4(sK1,k1_tarski(sK0),sK2),k1_tarski(sK0))
    | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f90,f39])).

fof(f90,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK0,X1)
      | r2_hidden(sK1,k11_relat_1(sK2,sK0))
      | r2_hidden(sK4(sK1,X1,sK2),X1) ) ),
    inference(resolution,[],[f87,f50])).

fof(f87,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k9_relat_1(sK2,X0))
      | ~ r2_hidden(sK0,X0)
      | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ) ),
    inference(global_subsumption,[],[f45,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | r2_hidden(sK1,k9_relat_1(sK2,X0))
      | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ) ),
    inference(resolution,[],[f84,f25])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X2),sK2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(X2,k9_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f37,f24])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,
    ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f44,f25])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f32,f24])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,sK2),X0),sK2)
      | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f35,f24])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f25,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,
    ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f114,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k11_relat_1(sK2,X0))
      | ~ r2_hidden(sK0,k1_tarski(X0)) ) ),
    inference(subsumption_resolution,[],[f91,f109])).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k11_relat_1(sK2,X0))
      | ~ r2_hidden(sK0,k1_tarski(X0))
      | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ) ),
    inference(superposition,[],[f87,f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:13:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (6753)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.50  % (6739)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (6751)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (6756)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (6735)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (6745)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (6743)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (6749)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.23/0.51  % (6733)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.51  % (6748)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.23/0.51  % (6745)Refutation found. Thanks to Tanya!
% 1.23/0.51  % SZS status Theorem for theBenchmark
% 1.23/0.51  % (6732)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.23/0.51  % (6739)Refutation not found, incomplete strategy% (6739)------------------------------
% 1.23/0.51  % (6739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.51  % (6739)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.51  
% 1.23/0.51  % (6739)Memory used [KB]: 1663
% 1.23/0.51  % (6739)Time elapsed: 0.094 s
% 1.23/0.51  % (6739)------------------------------
% 1.23/0.51  % (6739)------------------------------
% 1.23/0.51  % (6752)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.23/0.51  % (6755)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.23/0.51  % (6747)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.23/0.51  % (6734)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.23/0.52  % (6737)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.23/0.52  % (6733)Refutation not found, incomplete strategy% (6733)------------------------------
% 1.23/0.52  % (6733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (6733)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.52  
% 1.23/0.52  % (6733)Memory used [KB]: 10618
% 1.23/0.52  % (6733)Time elapsed: 0.096 s
% 1.23/0.52  % (6733)------------------------------
% 1.23/0.52  % (6733)------------------------------
% 1.23/0.52  % (6732)Refutation not found, incomplete strategy% (6732)------------------------------
% 1.23/0.52  % (6732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (6746)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.23/0.52  % (6732)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.52  
% 1.23/0.52  % (6732)Memory used [KB]: 10618
% 1.23/0.52  % (6732)Time elapsed: 0.103 s
% 1.23/0.52  % (6732)------------------------------
% 1.23/0.52  % (6732)------------------------------
% 1.23/0.52  % (6744)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.23/0.52  % (6758)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.23/0.52  % (6754)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.23/0.52  % (6741)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.23/0.52  % (6746)Refutation not found, incomplete strategy% (6746)------------------------------
% 1.23/0.52  % (6746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (6746)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.52  
% 1.23/0.52  % (6746)Memory used [KB]: 6268
% 1.23/0.52  % (6746)Time elapsed: 0.110 s
% 1.23/0.52  % (6746)------------------------------
% 1.23/0.52  % (6746)------------------------------
% 1.23/0.52  % (6750)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.23/0.52  % (6736)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.23/0.52  % (6738)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.23/0.53  % SZS output start Proof for theBenchmark
% 1.23/0.53  fof(f127,plain,(
% 1.23/0.53    $false),
% 1.23/0.53    inference(resolution,[],[f124,f39])).
% 1.23/0.53  fof(f39,plain,(
% 1.23/0.53    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.23/0.53    inference(equality_resolution,[],[f38])).
% 1.23/0.53  fof(f38,plain,(
% 1.23/0.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.23/0.53    inference(equality_resolution,[],[f29])).
% 1.23/0.53  fof(f29,plain,(
% 1.23/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.23/0.53    inference(cnf_transformation,[],[f19])).
% 1.23/0.53  fof(f19,plain,(
% 1.23/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 1.23/0.53  fof(f18,plain,(
% 1.23/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.23/0.53    introduced(choice_axiom,[])).
% 1.23/0.53  fof(f17,plain,(
% 1.23/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.23/0.53    inference(rectify,[],[f16])).
% 1.23/0.53  fof(f16,plain,(
% 1.23/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.23/0.53    inference(nnf_transformation,[],[f1])).
% 1.23/0.53  fof(f1,axiom,(
% 1.23/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.23/0.53  fof(f124,plain,(
% 1.23/0.53    ~r2_hidden(sK0,k1_tarski(sK0))),
% 1.23/0.53    inference(resolution,[],[f114,f109])).
% 1.23/0.53  fof(f109,plain,(
% 1.23/0.53    ~r2_hidden(sK1,k11_relat_1(sK2,sK0))),
% 1.23/0.53    inference(subsumption_resolution,[],[f26,f108])).
% 1.23/0.53  fof(f108,plain,(
% 1.23/0.53    r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.23/0.53    inference(global_subsumption,[],[f25,f107])).
% 1.23/0.53  fof(f107,plain,(
% 1.23/0.53    ~r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.23/0.53    inference(forward_demodulation,[],[f103,f43])).
% 1.23/0.53  fof(f43,plain,(
% 1.23/0.53    ( ! [X0] : (k11_relat_1(sK2,X0) = k9_relat_1(sK2,k1_tarski(X0))) )),
% 1.23/0.53    inference(resolution,[],[f27,f24])).
% 1.23/0.53  fof(f24,plain,(
% 1.23/0.53    v1_relat_1(sK2)),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  fof(f15,plain,(
% 1.23/0.53    (~r2_hidden(sK1,k11_relat_1(sK2,sK0)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & (r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & v1_relat_1(sK2)),
% 1.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 1.23/0.53  fof(f14,plain,(
% 1.23/0.53    ? [X0,X1,X2] : ((~r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2)) => ((~r2_hidden(sK1,k11_relat_1(sK2,sK0)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & (r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & v1_relat_1(sK2))),
% 1.23/0.53    introduced(choice_axiom,[])).
% 1.23/0.53  fof(f13,plain,(
% 1.23/0.53    ? [X0,X1,X2] : ((~r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) & v1_relat_1(X2))),
% 1.23/0.53    inference(flattening,[],[f12])).
% 1.23/0.53  fof(f12,plain,(
% 1.23/0.53    ? [X0,X1,X2] : (((~r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2))) & v1_relat_1(X2))),
% 1.23/0.53    inference(nnf_transformation,[],[f7])).
% 1.23/0.53  fof(f7,plain,(
% 1.23/0.53    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r2_hidden(X1,k11_relat_1(X2,X0))) & v1_relat_1(X2))),
% 1.23/0.53    inference(ennf_transformation,[],[f6])).
% 1.23/0.53  fof(f6,negated_conjecture,(
% 1.23/0.53    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 1.23/0.53    inference(negated_conjecture,[],[f5])).
% 1.23/0.53  fof(f5,conjecture,(
% 1.23/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 1.23/0.53  fof(f27,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 1.23/0.53    inference(cnf_transformation,[],[f8])).
% 1.23/0.53  fof(f8,plain,(
% 1.23/0.53    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.23/0.53    inference(ennf_transformation,[],[f2])).
% 1.23/0.53  fof(f2,axiom,(
% 1.23/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 1.23/0.53  fof(f103,plain,(
% 1.23/0.53    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(sK1,k9_relat_1(sK2,k1_tarski(sK0)))),
% 1.23/0.53    inference(superposition,[],[f58,f99])).
% 1.23/0.53  fof(f99,plain,(
% 1.23/0.53    sK0 = sK4(sK1,k1_tarski(sK0),sK2)),
% 1.23/0.53    inference(duplicate_literal_removal,[],[f98])).
% 1.23/0.53  fof(f98,plain,(
% 1.23/0.53    sK0 = sK4(sK1,k1_tarski(sK0),sK2) | sK0 = sK4(sK1,k1_tarski(sK0),sK2)),
% 1.23/0.53    inference(resolution,[],[f95,f52])).
% 1.23/0.53  fof(f52,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k11_relat_1(sK2,X1)) | sK4(X0,k1_tarski(X1),sK2) = X1) )),
% 1.23/0.53    inference(resolution,[],[f51,f40])).
% 1.23/0.53  fof(f40,plain,(
% 1.23/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.23/0.53    inference(equality_resolution,[],[f28])).
% 1.23/0.53  fof(f28,plain,(
% 1.23/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.23/0.53    inference(cnf_transformation,[],[f19])).
% 1.23/0.53  fof(f51,plain,(
% 1.23/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X1,k1_tarski(X0),sK2),k1_tarski(X0)) | ~r2_hidden(X1,k11_relat_1(sK2,X0))) )),
% 1.23/0.53    inference(superposition,[],[f50,f43])).
% 1.23/0.53  fof(f50,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK2,X1)) | r2_hidden(sK4(X0,X1,sK2),X1)) )),
% 1.23/0.53    inference(resolution,[],[f36,f24])).
% 1.23/0.53  fof(f36,plain,(
% 1.23/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK4(X0,X1,X2),X1)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f23])).
% 1.23/0.53  fof(f23,plain,(
% 1.23/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 1.23/0.53  fof(f22,plain,(
% 1.23/0.53    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))))),
% 1.23/0.53    introduced(choice_axiom,[])).
% 1.23/0.53  fof(f21,plain,(
% 1.23/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.23/0.53    inference(rectify,[],[f20])).
% 1.23/0.53  fof(f20,plain,(
% 1.23/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.23/0.53    inference(nnf_transformation,[],[f11])).
% 1.23/0.53  fof(f11,plain,(
% 1.23/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.23/0.53    inference(ennf_transformation,[],[f3])).
% 1.23/0.53  fof(f3,axiom,(
% 1.23/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 1.23/0.53  fof(f95,plain,(
% 1.23/0.53    r2_hidden(sK1,k11_relat_1(sK2,sK0)) | sK0 = sK4(sK1,k1_tarski(sK0),sK2)),
% 1.23/0.53    inference(resolution,[],[f93,f40])).
% 1.23/0.53  fof(f93,plain,(
% 1.23/0.53    r2_hidden(sK4(sK1,k1_tarski(sK0),sK2),k1_tarski(sK0)) | r2_hidden(sK1,k11_relat_1(sK2,sK0))),
% 1.23/0.53    inference(resolution,[],[f90,f39])).
% 1.23/0.53  fof(f90,plain,(
% 1.23/0.53    ( ! [X1] : (~r2_hidden(sK0,X1) | r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(sK4(sK1,X1,sK2),X1)) )),
% 1.23/0.53    inference(resolution,[],[f87,f50])).
% 1.23/0.53  fof(f87,plain,(
% 1.23/0.53    ( ! [X0] : (r2_hidden(sK1,k9_relat_1(sK2,X0)) | ~r2_hidden(sK0,X0) | r2_hidden(sK1,k11_relat_1(sK2,sK0))) )),
% 1.23/0.53    inference(global_subsumption,[],[f45,f85])).
% 1.23/0.53  fof(f85,plain,(
% 1.23/0.53    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK1,k9_relat_1(sK2,X0)) | r2_hidden(sK1,k11_relat_1(sK2,sK0))) )),
% 1.23/0.53    inference(resolution,[],[f84,f25])).
% 1.23/0.53  fof(f84,plain,(
% 1.23/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X2),sK2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(X2,k9_relat_1(sK2,X1))) )),
% 1.23/0.53    inference(resolution,[],[f37,f24])).
% 1.23/0.53  fof(f37,plain,(
% 1.23/0.53    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 1.23/0.53    inference(cnf_transformation,[],[f23])).
% 1.23/0.53  fof(f45,plain,(
% 1.23/0.53    r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(sK0,k1_relat_1(sK2))),
% 1.23/0.53    inference(resolution,[],[f44,f25])).
% 1.23/0.53  fof(f44,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(X0,k1_relat_1(sK2))) )),
% 1.23/0.53    inference(resolution,[],[f32,f24])).
% 1.23/0.53  fof(f32,plain,(
% 1.23/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 1.23/0.53    inference(cnf_transformation,[],[f10])).
% 1.23/0.53  fof(f10,plain,(
% 1.23/0.53    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.23/0.53    inference(flattening,[],[f9])).
% 1.23/0.53  fof(f9,plain,(
% 1.23/0.53    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.23/0.53    inference(ennf_transformation,[],[f4])).
% 1.23/0.53  fof(f4,axiom,(
% 1.23/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 1.23/0.53  fof(f58,plain,(
% 1.23/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1,sK2),X0),sK2) | ~r2_hidden(X0,k9_relat_1(sK2,X1))) )),
% 1.23/0.53    inference(resolution,[],[f35,f24])).
% 1.23/0.53  fof(f35,plain,(
% 1.23/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f23])).
% 1.23/0.53  fof(f25,plain,(
% 1.23/0.53    r2_hidden(k4_tarski(sK0,sK1),sK2) | r2_hidden(sK1,k11_relat_1(sK2,sK0))),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  fof(f26,plain,(
% 1.23/0.53    ~r2_hidden(sK1,k11_relat_1(sK2,sK0)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  fof(f114,plain,(
% 1.23/0.53    ( ! [X0] : (r2_hidden(sK1,k11_relat_1(sK2,X0)) | ~r2_hidden(sK0,k1_tarski(X0))) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f91,f109])).
% 1.23/0.53  fof(f91,plain,(
% 1.23/0.53    ( ! [X0] : (r2_hidden(sK1,k11_relat_1(sK2,X0)) | ~r2_hidden(sK0,k1_tarski(X0)) | r2_hidden(sK1,k11_relat_1(sK2,sK0))) )),
% 1.23/0.53    inference(superposition,[],[f87,f43])).
% 1.23/0.53  % SZS output end Proof for theBenchmark
% 1.23/0.53  % (6745)------------------------------
% 1.23/0.53  % (6745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (6745)Termination reason: Refutation
% 1.23/0.53  
% 1.23/0.53  % (6745)Memory used [KB]: 6268
% 1.23/0.53  % (6745)Time elapsed: 0.106 s
% 1.23/0.53  % (6745)------------------------------
% 1.23/0.53  % (6745)------------------------------
% 1.23/0.53  % (6731)Success in time 0.171 s
%------------------------------------------------------------------------------
