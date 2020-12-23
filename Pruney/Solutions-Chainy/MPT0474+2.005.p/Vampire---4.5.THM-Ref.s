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
% DateTime   : Thu Dec  3 12:48:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 (  88 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  184 ( 250 expanded)
%              Number of equality atoms :   44 (  75 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f227,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f62,f173,f192,f222,f225])).

fof(f225,plain,
    ( ~ spl2_14
    | ~ spl2_17 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f223,f211])).

fof(f211,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl2_17 ),
    inference(superposition,[],[f28,f196])).

fof(f196,plain,
    ( ! [X0] : o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0)
    | ~ spl2_17 ),
    inference(backward_demodulation,[],[f31,f184])).

fof(f184,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl2_17
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f28,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f223,plain,
    ( r2_hidden(k4_tarski(sK0(o_0_0_xboole_0,o_0_0_xboole_0),sK1(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f172,f184])).

fof(f172,plain,
    ( r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl2_14
  <=> r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f222,plain,
    ( ~ spl2_13
    | ~ spl2_17 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl2_13
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f220,f211])).

fof(f220,plain,
    ( r2_hidden(k4_tarski(sK1(o_0_0_xboole_0,o_0_0_xboole_0),sK0(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl2_13
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f168,f184])).

fof(f168,plain,
    ( r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl2_13
  <=> r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f192,plain,(
    spl2_17 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl2_17 ),
    inference(trivial_inequality_removal,[],[f190])).

fof(f190,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | spl2_17 ),
    inference(resolution,[],[f187,f30])).

fof(f30,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f187,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 != X0 )
    | spl2_17 ),
    inference(superposition,[],[f185,f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f185,plain,
    ( o_0_0_xboole_0 != k1_xboole_0
    | spl2_17 ),
    inference(avatar_component_clause,[],[f183])).

fof(f173,plain,
    ( spl2_13
    | spl2_14
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f163,f45,f41,f170,f166])).

fof(f41,plain,
    ( spl2_1
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f45,plain,
    ( spl2_2
  <=> ! [X0] :
        ( k1_xboole_0 != X0
        | ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK0(k1_xboole_0,X0),sK1(k1_xboole_0,X0)),X0)
        | r2_hidden(k4_tarski(sK1(k1_xboole_0,X0),sK0(k1_xboole_0,X0)),k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f163,plain,
    ( r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f161])).

fof(f161,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f46,f42])).

fof(f42,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f46,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 != X0
        | r2_hidden(k4_tarski(sK0(k1_xboole_0,X0),sK1(k1_xboole_0,X0)),X0)
        | r2_hidden(k4_tarski(sK1(k1_xboole_0,X0),sK0(k1_xboole_0,X0)),k1_xboole_0) )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f62,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f56,f30])).

fof(f56,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f53,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f53,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | spl2_1 ),
    inference(superposition,[],[f43,f27])).

fof(f43,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f47,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f38,f45,f41])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r2_hidden(k4_tarski(sK1(k1_xboole_0,X0),sK0(k1_xboole_0,X0)),k1_xboole_0)
      | r2_hidden(k4_tarski(sK0(k1_xboole_0,X0),sK1(k1_xboole_0,X0)),X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f19,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(f19,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f8])).

fof(f8,negated_conjecture,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:49:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (24454)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.47  % (24454)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (24446)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.47  % (24438)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f227,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f47,f62,f173,f192,f222,f225])).
% 0.22/0.48  fof(f225,plain,(
% 0.22/0.48    ~spl2_14 | ~spl2_17),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f224])).
% 0.22/0.48  fof(f224,plain,(
% 0.22/0.48    $false | (~spl2_14 | ~spl2_17)),
% 0.22/0.48    inference(subsumption_resolution,[],[f223,f211])).
% 0.22/0.48  fof(f211,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,o_0_0_xboole_0)) ) | ~spl2_17),
% 0.22/0.48    inference(superposition,[],[f28,f196])).
% 0.22/0.48  fof(f196,plain,(
% 0.22/0.48    ( ! [X0] : (o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0)) ) | ~spl2_17),
% 0.22/0.48    inference(backward_demodulation,[],[f31,f184])).
% 0.22/0.48  fof(f184,plain,(
% 0.22/0.48    o_0_0_xboole_0 = k1_xboole_0 | ~spl2_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f183])).
% 0.22/0.48  fof(f183,plain,(
% 0.22/0.48    spl2_17 <=> o_0_0_xboole_0 = k1_xboole_0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.48    inference(flattening,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.48    inference(nnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.48  fof(f223,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK0(o_0_0_xboole_0,o_0_0_xboole_0),sK1(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0) | (~spl2_14 | ~spl2_17)),
% 0.22/0.48    inference(forward_demodulation,[],[f172,f184])).
% 0.22/0.48  fof(f172,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl2_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f170])).
% 0.22/0.48  fof(f170,plain,(
% 0.22/0.48    spl2_14 <=> r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.48  fof(f222,plain,(
% 0.22/0.48    ~spl2_13 | ~spl2_17),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f221])).
% 0.22/0.48  fof(f221,plain,(
% 0.22/0.48    $false | (~spl2_13 | ~spl2_17)),
% 0.22/0.48    inference(subsumption_resolution,[],[f220,f211])).
% 0.22/0.48  fof(f220,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK1(o_0_0_xboole_0,o_0_0_xboole_0),sK0(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0) | (~spl2_13 | ~spl2_17)),
% 0.22/0.48    inference(forward_demodulation,[],[f168,f184])).
% 0.22/0.48  fof(f168,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl2_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f166])).
% 0.22/0.48  fof(f166,plain,(
% 0.22/0.48    spl2_13 <=> r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.48  fof(f192,plain,(
% 0.22/0.48    spl2_17),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f191])).
% 0.22/0.48  fof(f191,plain,(
% 0.22/0.48    $false | spl2_17),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f190])).
% 0.22/0.48  fof(f190,plain,(
% 0.22/0.48    o_0_0_xboole_0 != o_0_0_xboole_0 | spl2_17),
% 0.22/0.48    inference(resolution,[],[f187,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    v1_xboole_0(o_0_0_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    v1_xboole_0(o_0_0_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 0.22/0.48  fof(f187,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(X0) | o_0_0_xboole_0 != X0) ) | spl2_17),
% 0.22/0.48    inference(superposition,[],[f185,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.48  fof(f185,plain,(
% 0.22/0.48    o_0_0_xboole_0 != k1_xboole_0 | spl2_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f183])).
% 0.22/0.48  fof(f173,plain,(
% 0.22/0.48    spl2_13 | spl2_14 | ~spl2_1 | ~spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f163,f45,f41,f170,f166])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    spl2_1 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    spl2_2 <=> ! [X0] : (k1_xboole_0 != X0 | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK0(k1_xboole_0,X0),sK1(k1_xboole_0,X0)),X0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,X0),sK0(k1_xboole_0,X0)),k1_xboole_0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.48  fof(f163,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | (~spl2_1 | ~spl2_2)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f161])).
% 0.22/0.48  fof(f161,plain,(
% 0.22/0.48    k1_xboole_0 != k1_xboole_0 | r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | (~spl2_1 | ~spl2_2)),
% 0.22/0.48    inference(resolution,[],[f46,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    v1_relat_1(k1_xboole_0) | ~spl2_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f41])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != X0 | r2_hidden(k4_tarski(sK0(k1_xboole_0,X0),sK1(k1_xboole_0,X0)),X0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,X0),sK0(k1_xboole_0,X0)),k1_xboole_0)) ) | ~spl2_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f45])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl2_1),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    $false | spl2_1),
% 0.22/0.48    inference(resolution,[],[f56,f30])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(X0)) ) | spl2_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f53,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_xboole_0(X0)) ) | spl2_1),
% 0.22/0.48    inference(superposition,[],[f43,f27])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ~v1_relat_1(k1_xboole_0) | spl2_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f41])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ~spl2_1 | spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f38,f45,f41])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 != X0 | r2_hidden(k4_tarski(sK1(k1_xboole_0,X0),sK0(k1_xboole_0,X0)),k1_xboole_0) | r2_hidden(k4_tarski(sK0(k1_xboole_0,X0),sK1(k1_xboole_0,X0)),X0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.48    inference(superposition,[],[f19,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ((~r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(rectify,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X3,X2),X0)) & (r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,negated_conjecture,(
% 0.22/0.48    ~k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(negated_conjecture,[],[f7])).
% 0.22/0.48  fof(f7,conjecture,(
% 0.22/0.48    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (24454)------------------------------
% 0.22/0.48  % (24454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (24454)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (24454)Memory used [KB]: 6140
% 0.22/0.48  % (24454)Time elapsed: 0.061 s
% 0.22/0.48  % (24454)------------------------------
% 0.22/0.48  % (24454)------------------------------
% 0.22/0.49  % (24435)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (24439)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (24434)Success in time 0.124 s
%------------------------------------------------------------------------------
