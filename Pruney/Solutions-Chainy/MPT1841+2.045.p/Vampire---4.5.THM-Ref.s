%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 211 expanded)
%              Number of leaves         :   26 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  385 ( 760 expanded)
%              Number of equality atoms :   65 ( 129 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f426,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f90,f97,f101,f115,f165,f171,f184,f200,f413,f425])).

fof(f425,plain,(
    spl6_25 ),
    inference(avatar_contradiction_clause,[],[f423])).

fof(f423,plain,
    ( $false
    | spl6_25 ),
    inference(resolution,[],[f412,f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK3(X0),X0)
      & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f5,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f412,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(sK0))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f410])).

fof(f410,plain,
    ( spl6_25
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f413,plain,
    ( spl6_1
    | ~ spl6_25
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f408,f108,f410,f77])).

fof(f77,plain,
    ( spl6_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f108,plain,
    ( spl6_5
  <=> v1_xboole_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f408,plain,
    ( ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f205,f50])).

fof(f50,plain,(
    ! [X0] : ~ v1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f31])).

fof(f205,plain,
    ( ! [X0] :
        ( v1_subset_1(sK3(sK0),X0)
        | ~ m1_subset_1(sK3(sK0),k1_zfmisc_1(X0))
        | v1_xboole_0(X0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f110,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

% (9692)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_subset_1(X1,X0)
           => ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).

fof(f110,plain,
    ( v1_xboole_0(sK3(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f200,plain,
    ( ~ spl6_3
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(resolution,[],[f198,f118])).

fof(f118,plain,
    ( ~ v1_subset_1(sK0,sK0)
    | ~ spl6_6 ),
    inference(superposition,[],[f50,f114])).

fof(f114,plain,
    ( sK0 = sK3(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_6
  <=> sK0 = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f198,plain,
    ( v1_subset_1(sK0,sK0)
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f87,f197])).

fof(f197,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f164,f191])).

fof(f191,plain,
    ( sK1 = sK2(sK0)
    | ~ spl6_11 ),
    inference(resolution,[],[f183,f42])).

fof(f42,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f183,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK0)
        | sK2(sK0) = X1 )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl6_11
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,sK0)
        | sK2(sK0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f164,plain,
    ( sK0 = k1_tarski(sK2(sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl6_10
  <=> sK0 = k1_tarski(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f87,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl6_3
  <=> v1_subset_1(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f184,plain,
    ( spl6_1
    | spl6_11
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f175,f162,f182,f77])).

fof(f175,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK0)
        | v1_xboole_0(sK0)
        | sK2(sK0) = X1 )
    | ~ spl6_10 ),
    inference(superposition,[],[f67,f164])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_tarski(X0))
      | v1_xboole_0(k1_tarski(X0))
      | X0 = X1 ) ),
    inference(resolution,[],[f51,f64])).

fof(f64,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

% (9691)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (9683)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (9679)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (9684)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f37,plain,(
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
    inference(rectify,[],[f36])).

% (9692)Refutation not found, incomplete strategy% (9692)------------------------------
% (9692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9692)Termination reason: Refutation not found, incomplete strategy

% (9692)Memory used [KB]: 10618
% (9692)Time elapsed: 0.076 s
% (9692)------------------------------
% (9692)------------------------------
fof(f36,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f171,plain,(
    ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | ~ spl6_9 ),
    inference(resolution,[],[f160,f63])).

fof(f63,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f160,plain,
    ( ! [X5] : ~ r2_hidden(X5,k1_tarski(sK2(sK0)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl6_9
  <=> ! [X5] : ~ r2_hidden(X5,k1_tarski(sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f165,plain,
    ( spl6_1
    | spl6_9
    | spl6_10
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f152,f95,f162,f159,f77])).

fof(f95,plain,
    ( spl6_4
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | v1_xboole_0(X0)
        | sK0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f152,plain,
    ( ! [X5] :
        ( sK0 = k1_tarski(sK2(sK0))
        | ~ r2_hidden(X5,k1_tarski(sK2(sK0)))
        | v1_xboole_0(sK0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f146,f48])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
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

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK0)
        | k1_tarski(X1) = sK0
        | ~ r2_hidden(X0,k1_tarski(X1)) )
    | ~ spl6_4 ),
    inference(condensation,[],[f145])).

fof(f145,plain,
    ( ! [X4,X5,X3] :
        ( sK0 = k1_tarski(X3)
        | ~ r2_hidden(X3,sK0)
        | ~ r2_hidden(X4,k1_tarski(X3))
        | ~ r2_hidden(X5,k1_tarski(X3)) )
    | ~ spl6_4 ),
    inference(resolution,[],[f141,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f141,plain,
    ( ! [X4,X5] :
        ( v1_xboole_0(k1_tarski(X4))
        | sK0 = k1_tarski(X4)
        | ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X5,k1_tarski(X4)) )
    | ~ spl6_4 ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK0)
        | sK0 = k1_tarski(X4)
        | v1_xboole_0(k1_tarski(X4))
        | sK0 = k1_tarski(X4)
        | ~ r2_hidden(X5,k1_tarski(X4)) )
    | ~ spl6_4 ),
    inference(superposition,[],[f102,f133])).

fof(f133,plain,
    ( ! [X2,X3] :
        ( sK4(k1_tarski(X2),sK0) = X2
        | sK0 = k1_tarski(X2)
        | ~ r2_hidden(X3,k1_tarski(X2)) )
    | ~ spl6_4 ),
    inference(resolution,[],[f127,f47])).

fof(f127,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_tarski(X0))
        | k1_tarski(X0) = sK0
        | sK4(k1_tarski(X0),sK0) = X0 )
    | ~ spl6_4 ),
    inference(resolution,[],[f103,f64])).

fof(f103,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(X1,sK0),X1)
        | sK0 = X1
        | v1_xboole_0(X1) )
    | ~ spl6_4 ),
    inference(resolution,[],[f96,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f96,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | v1_xboole_0(X0)
        | sK0 = X0 )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,sK0),sK0)
        | sK0 = X0
        | v1_xboole_0(X0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f96,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f115,plain,
    ( spl6_5
    | spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f105,f95,f112,f108])).

fof(f105,plain,
    ( sK0 = sK3(sK0)
    | v1_xboole_0(sK3(sK0))
    | ~ spl6_4 ),
    inference(resolution,[],[f104,f49])).

fof(f104,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | sK0 = X2
        | v1_xboole_0(X2) )
    | ~ spl6_4 ),
    inference(resolution,[],[f96,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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

fof(f101,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | ~ spl6_1 ),
    inference(resolution,[],[f79,f41])).

fof(f41,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f97,plain,
    ( spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f93,f95,f77])).

fof(f93,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(sK0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f46,f44])).

fof(f44,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f90,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | spl6_2 ),
    inference(resolution,[],[f83,f42])).

fof(f83,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl6_2
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f88,plain,
    ( spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f75,f85,f81,f77])).

fof(f75,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f43,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f43,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (9674)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (9682)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (9687)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.50  % (9681)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (9682)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (9671)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (9699)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (9673)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (9670)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (9672)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (9672)Refutation not found, incomplete strategy% (9672)------------------------------
% 0.20/0.51  % (9672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9672)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9672)Memory used [KB]: 10618
% 0.20/0.51  % (9672)Time elapsed: 0.108 s
% 0.20/0.51  % (9672)------------------------------
% 0.20/0.51  % (9672)------------------------------
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f426,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f88,f90,f97,f101,f115,f165,f171,f184,f200,f413,f425])).
% 0.20/0.51  fof(f425,plain,(
% 0.20/0.51    spl6_25),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f423])).
% 0.20/0.51  fof(f423,plain,(
% 0.20/0.51    $false | spl6_25),
% 0.20/0.51    inference(resolution,[],[f412,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0] : (~v1_subset_1(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f5,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.20/0.51  fof(f412,plain,(
% 0.20/0.51    ~m1_subset_1(sK3(sK0),k1_zfmisc_1(sK0)) | spl6_25),
% 0.20/0.51    inference(avatar_component_clause,[],[f410])).
% 0.20/0.51  fof(f410,plain,(
% 0.20/0.51    spl6_25 <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.20/0.51  fof(f413,plain,(
% 0.20/0.51    spl6_1 | ~spl6_25 | ~spl6_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f408,f108,f410,f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    spl6_1 <=> v1_xboole_0(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    spl6_5 <=> v1_xboole_0(sK3(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.51  fof(f408,plain,(
% 0.20/0.51    ~m1_subset_1(sK3(sK0),k1_zfmisc_1(sK0)) | v1_xboole_0(sK0) | ~spl6_5),
% 0.20/0.51    inference(resolution,[],[f205,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_subset_1(sK3(X0),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f205,plain,(
% 0.20/0.51    ( ! [X0] : (v1_subset_1(sK3(sK0),X0) | ~m1_subset_1(sK3(sK0),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) ) | ~spl6_5),
% 0.20/0.51    inference(resolution,[],[f110,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  % (9692)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((~v1_xboole_0(X1) | v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_subset_1(X1,X0) => ~v1_xboole_0(X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    v1_xboole_0(sK3(sK0)) | ~spl6_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f108])).
% 0.20/0.51  fof(f200,plain,(
% 0.20/0.51    ~spl6_3 | ~spl6_6 | ~spl6_10 | ~spl6_11),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f199])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    $false | (~spl6_3 | ~spl6_6 | ~spl6_10 | ~spl6_11)),
% 0.20/0.51    inference(resolution,[],[f198,f118])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    ~v1_subset_1(sK0,sK0) | ~spl6_6),
% 0.20/0.51    inference(superposition,[],[f50,f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    sK0 = sK3(sK0) | ~spl6_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f112])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    spl6_6 <=> sK0 = sK3(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    v1_subset_1(sK0,sK0) | (~spl6_3 | ~spl6_10 | ~spl6_11)),
% 0.20/0.51    inference(backward_demodulation,[],[f87,f197])).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    sK0 = k1_tarski(sK1) | (~spl6_10 | ~spl6_11)),
% 0.20/0.51    inference(backward_demodulation,[],[f164,f191])).
% 0.20/0.51  fof(f191,plain,(
% 0.20/0.51    sK1 = sK2(sK0) | ~spl6_11),
% 0.20/0.51    inference(resolution,[],[f183,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    m1_subset_1(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f24,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.51    inference(negated_conjecture,[],[f10])).
% 0.20/0.51  fof(f10,conjecture,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    ( ! [X1] : (~m1_subset_1(X1,sK0) | sK2(sK0) = X1) ) | ~spl6_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f182])).
% 0.20/0.51  fof(f182,plain,(
% 0.20/0.51    spl6_11 <=> ! [X1] : (~m1_subset_1(X1,sK0) | sK2(sK0) = X1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.51  fof(f164,plain,(
% 0.20/0.51    sK0 = k1_tarski(sK2(sK0)) | ~spl6_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f162])).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    spl6_10 <=> sK0 = k1_tarski(sK2(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    v1_subset_1(k1_tarski(sK1),sK0) | ~spl6_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    spl6_3 <=> v1_subset_1(k1_tarski(sK1),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    spl6_1 | spl6_11 | ~spl6_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f175,f162,f182,f77])).
% 0.20/0.51  fof(f175,plain,(
% 0.20/0.51    ( ! [X1] : (~m1_subset_1(X1,sK0) | v1_xboole_0(sK0) | sK2(sK0) = X1) ) | ~spl6_10),
% 0.20/0.51    inference(superposition,[],[f67,f164])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_tarski(X0)) | v1_xboole_0(k1_tarski(X0)) | X0 = X1) )),
% 0.20/0.51    inference(resolution,[],[f51,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.20/0.51    inference(equality_resolution,[],[f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.52  % (9691)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (9683)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (9679)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (9684)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.52    inference(rectify,[],[f36])).
% 0.20/0.52  % (9692)Refutation not found, incomplete strategy% (9692)------------------------------
% 0.20/0.52  % (9692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (9692)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (9692)Memory used [KB]: 10618
% 0.20/0.52  % (9692)Time elapsed: 0.076 s
% 0.20/0.52  % (9692)------------------------------
% 0.20/0.52  % (9692)------------------------------
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.52  fof(f171,plain,(
% 0.20/0.52    ~spl6_9),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f166])).
% 0.20/0.52  fof(f166,plain,(
% 0.20/0.52    $false | ~spl6_9),
% 0.20/0.52    inference(resolution,[],[f160,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.20/0.52    inference(equality_resolution,[],[f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.20/0.52    inference(equality_resolution,[],[f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    ( ! [X5] : (~r2_hidden(X5,k1_tarski(sK2(sK0)))) ) | ~spl6_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f159])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    spl6_9 <=> ! [X5] : ~r2_hidden(X5,k1_tarski(sK2(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.52  fof(f165,plain,(
% 0.20/0.52    spl6_1 | spl6_9 | spl6_10 | ~spl6_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f152,f95,f162,f159,f77])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    spl6_4 <=> ! [X0] : (~r1_tarski(X0,sK0) | v1_xboole_0(X0) | sK0 = X0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    ( ! [X5] : (sK0 = k1_tarski(sK2(sK0)) | ~r2_hidden(X5,k1_tarski(sK2(sK0))) | v1_xboole_0(sK0)) ) | ~spl6_4),
% 0.20/0.52    inference(resolution,[],[f146,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.52    inference(rectify,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | k1_tarski(X1) = sK0 | ~r2_hidden(X0,k1_tarski(X1))) ) | ~spl6_4),
% 0.20/0.52    inference(condensation,[],[f145])).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    ( ! [X4,X5,X3] : (sK0 = k1_tarski(X3) | ~r2_hidden(X3,sK0) | ~r2_hidden(X4,k1_tarski(X3)) | ~r2_hidden(X5,k1_tarski(X3))) ) | ~spl6_4),
% 0.20/0.52    inference(resolution,[],[f141,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    ( ! [X4,X5] : (v1_xboole_0(k1_tarski(X4)) | sK0 = k1_tarski(X4) | ~r2_hidden(X4,sK0) | ~r2_hidden(X5,k1_tarski(X4))) ) | ~spl6_4),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f140])).
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    ( ! [X4,X5] : (~r2_hidden(X4,sK0) | sK0 = k1_tarski(X4) | v1_xboole_0(k1_tarski(X4)) | sK0 = k1_tarski(X4) | ~r2_hidden(X5,k1_tarski(X4))) ) | ~spl6_4),
% 0.20/0.52    inference(superposition,[],[f102,f133])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    ( ! [X2,X3] : (sK4(k1_tarski(X2),sK0) = X2 | sK0 = k1_tarski(X2) | ~r2_hidden(X3,k1_tarski(X2))) ) | ~spl6_4),
% 0.20/0.52    inference(resolution,[],[f127,f47])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    ( ! [X0] : (v1_xboole_0(k1_tarski(X0)) | k1_tarski(X0) = sK0 | sK4(k1_tarski(X0),sK0) = X0) ) | ~spl6_4),
% 0.20/0.52    inference(resolution,[],[f103,f64])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    ( ! [X1] : (r2_hidden(sK4(X1,sK0),X1) | sK0 = X1 | v1_xboole_0(X1)) ) | ~spl6_4),
% 0.20/0.52    inference(resolution,[],[f96,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(rectify,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,sK0) | v1_xboole_0(X0) | sK0 = X0) ) | ~spl6_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f95])).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK4(X0,sK0),sK0) | sK0 = X0 | v1_xboole_0(X0)) ) | ~spl6_4),
% 0.20/0.52    inference(resolution,[],[f96,f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    spl6_5 | spl6_6 | ~spl6_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f105,f95,f112,f108])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    sK0 = sK3(sK0) | v1_xboole_0(sK3(sK0)) | ~spl6_4),
% 0.20/0.52    inference(resolution,[],[f104,f49])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK0)) | sK0 = X2 | v1_xboole_0(X2)) ) | ~spl6_4),
% 0.20/0.52    inference(resolution,[],[f96,f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    ~spl6_1),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f98])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    $false | ~spl6_1),
% 0.20/0.52    inference(resolution,[],[f79,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ~v1_xboole_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    v1_xboole_0(sK0) | ~spl6_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f77])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    spl6_1 | spl6_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f93,f95,f77])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(sK0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(resolution,[],[f46,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    v1_zfmisc_1(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    spl6_2),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f89])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    $false | spl6_2),
% 0.20/0.52    inference(resolution,[],[f83,f42])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,sK0) | spl6_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    spl6_2 <=> m1_subset_1(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    spl6_1 | ~spl6_2 | spl6_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f75,f85,f81,f77])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    v1_subset_1(k1_tarski(sK1),sK0) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0)),
% 0.20/0.52    inference(superposition,[],[f43,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.52    inference(flattening,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (9682)------------------------------
% 0.20/0.52  % (9682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (9682)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (9682)Memory used [KB]: 6396
% 0.20/0.52  % (9682)Time elapsed: 0.100 s
% 0.20/0.52  % (9682)------------------------------
% 0.20/0.52  % (9682)------------------------------
% 0.20/0.53  % (9669)Success in time 0.166 s
%------------------------------------------------------------------------------
