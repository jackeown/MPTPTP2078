%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 132 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  242 ( 439 expanded)
%              Number of equality atoms :   26 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f109,f120,f127,f130,f133,f194,f219])).

fof(f219,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f201,f206])).

fof(f206,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_xboole_0)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f197,f198])).

fof(f198,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f56,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
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

fof(f56,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_1
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f197,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_zfmisc_1(sK0))
    | ~ spl5_1 ),
    inference(resolution,[],[f56,f32])).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f201,plain,
    ( r2_hidden(k1_enumset1(sK1,sK1,sK2),k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f59,f198])).

fof(f59,plain,
    ( r2_hidden(k1_enumset1(sK1,sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_2
  <=> r2_hidden(k1_enumset1(sK1,sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f194,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | ~ spl5_7 ),
    inference(trivial_inequality_removal,[],[f192])).

fof(f192,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl5_7 ),
    inference(superposition,[],[f29,f137])).

fof(f137,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_7 ),
    inference(resolution,[],[f115,f31])).

fof(f115,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_7
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f29,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f14,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
            & k1_xboole_0 != X0
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0))
          & k1_xboole_0 != sK0
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ~ m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0))
        & k1_xboole_0 != sK0
        & m1_subset_1(X2,sK0) )
   => ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
      & k1_xboole_0 != sK0
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ( k1_xboole_0 != X0
             => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ( k1_xboole_0 != X0
           => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_subset_1)).

fof(f133,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl5_9 ),
    inference(resolution,[],[f126,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f126,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_9
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f130,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl5_8 ),
    inference(resolution,[],[f119,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f119,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_8
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f127,plain,
    ( spl5_7
    | ~ spl5_9
    | spl5_6 ),
    inference(avatar_split_clause,[],[f122,f106,f124,f113])).

fof(f106,plain,
    ( spl5_6
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f122,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0)
    | spl5_6 ),
    inference(resolution,[],[f108,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f108,plain,
    ( ~ r2_hidden(sK2,sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f120,plain,
    ( spl5_7
    | ~ spl5_8
    | spl5_5 ),
    inference(avatar_split_clause,[],[f111,f102,f117,f113])).

fof(f102,plain,
    ( spl5_5
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f111,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | spl5_5 ),
    inference(resolution,[],[f104,f35])).

fof(f104,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f109,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | spl5_2 ),
    inference(avatar_split_clause,[],[f98,f58,f106,f102])).

fof(f98,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ r2_hidden(sK1,sK0)
    | spl5_2 ),
    inference(resolution,[],[f47,f62])).

fof(f62,plain,
    ( ~ r1_tarski(k1_enumset1(sK1,sK1,sK2),sK0)
    | spl5_2 ),
    inference(resolution,[],[f60,f50])).

fof(f50,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f60,plain,
    ( ~ r2_hidden(k1_enumset1(sK1,sK1,sK2),k1_zfmisc_1(sK0))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f45,f34])).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f61,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f52,f58,f54])).

fof(f52,plain,
    ( ~ r2_hidden(k1_enumset1(sK1,sK1,sK2),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f36,f46])).

fof(f46,plain,(
    ~ m1_subset_1(k1_enumset1(sK1,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f30,plain,(
    ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:30:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (29940)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (29930)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (29940)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f220,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f61,f109,f120,f127,f130,f133,f194,f219])).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    ~spl5_1 | ~spl5_2),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f218])).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    $false | (~spl5_1 | ~spl5_2)),
% 0.22/0.50    inference(resolution,[],[f201,f206])).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) ) | ~spl5_1),
% 0.22/0.50    inference(backward_demodulation,[],[f197,f198])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    k1_xboole_0 = k1_zfmisc_1(sK0) | ~spl5_1),
% 0.22/0.50    inference(resolution,[],[f56,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    spl5_1 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    ( ! [X2] : (~r2_hidden(X2,k1_zfmisc_1(sK0))) ) | ~spl5_1),
% 0.22/0.50    inference(resolution,[],[f56,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.50    inference(rectify,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    r2_hidden(k1_enumset1(sK1,sK1,sK2),k1_xboole_0) | (~spl5_1 | ~spl5_2)),
% 0.22/0.50    inference(backward_demodulation,[],[f59,f198])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    r2_hidden(k1_enumset1(sK1,sK1,sK2),k1_zfmisc_1(sK0)) | ~spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    spl5_2 <=> r2_hidden(k1_enumset1(sK1,sK1,sK2),k1_zfmisc_1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    ~spl5_7),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f193])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    $false | ~spl5_7),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f192])).
% 0.22/0.50  fof(f192,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | ~spl5_7),
% 0.22/0.50    inference(superposition,[],[f29,f137])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | ~spl5_7),
% 0.22/0.50    inference(resolution,[],[f115,f31])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    v1_xboole_0(sK0) | ~spl5_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f113])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl5_7 <=> v1_xboole_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    k1_xboole_0 != sK0),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    (~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f14,f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0,X1] : (? [X2] : (~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) => (? [X2] : (~m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X2] : (~m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(X2,sK0)) => (~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK2,sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0,X1] : (? [X2] : (~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 0.22/0.50    inference(flattening,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ? [X0,X1] : (? [X2] : ((~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f7])).
% 0.22/0.50  fof(f7,conjecture,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_subset_1)).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl5_9),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f131])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    $false | spl5_9),
% 0.22/0.50    inference(resolution,[],[f126,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    m1_subset_1(sK2,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,sK0) | spl5_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f124])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    spl5_9 <=> m1_subset_1(sK2,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    spl5_8),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f128])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    $false | spl5_8),
% 0.22/0.50    inference(resolution,[],[f119,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    m1_subset_1(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,sK0) | spl5_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f117])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    spl5_8 <=> m1_subset_1(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    spl5_7 | ~spl5_9 | spl5_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f122,f106,f124,f113])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    spl5_6 <=> r2_hidden(sK2,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,sK0) | v1_xboole_0(sK0) | spl5_6),
% 0.22/0.50    inference(resolution,[],[f108,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(nnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ~r2_hidden(sK2,sK0) | spl5_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f106])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    spl5_7 | ~spl5_8 | spl5_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f111,f102,f117,f113])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    spl5_5 <=> r2_hidden(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | spl5_5),
% 0.22/0.50    inference(resolution,[],[f104,f35])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    ~r2_hidden(sK1,sK0) | spl5_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f102])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    ~spl5_5 | ~spl5_6 | spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f98,f58,f106,f102])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ~r2_hidden(sK2,sK0) | ~r2_hidden(sK1,sK0) | spl5_2),
% 0.22/0.50    inference(resolution,[],[f47,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ~r1_tarski(k1_enumset1(sK1,sK1,sK2),sK0) | spl5_2),
% 0.22/0.50    inference(resolution,[],[f60,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.50    inference(rectify,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ~r2_hidden(k1_enumset1(sK1,sK1,sK2),k1_zfmisc_1(sK0)) | spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f58])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f45,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.50    inference(flattening,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.50    inference(nnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl5_1 | ~spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f52,f58,f54])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ~r2_hidden(k1_enumset1(sK1,sK1,sK2),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(resolution,[],[f36,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ~m1_subset_1(k1_enumset1(sK1,sK1,sK2),k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(definition_unfolding,[],[f30,f34])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (29940)------------------------------
% 0.22/0.50  % (29940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (29940)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (29940)Memory used [KB]: 6268
% 0.22/0.50  % (29940)Time elapsed: 0.090 s
% 0.22/0.50  % (29940)------------------------------
% 0.22/0.50  % (29940)------------------------------
% 0.22/0.50  % (29927)Success in time 0.13 s
%------------------------------------------------------------------------------
