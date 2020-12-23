%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  74 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :  167 ( 318 expanded)
%              Number of equality atoms :   22 (  50 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f42,f109,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sQ4_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f27,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f109,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f108,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13,f12])).

fof(f12,plain,
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

fof(f13,plain,
    ( ? [X2] :
        ( ~ m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0))
        & k1_xboole_0 != sK0
        & m1_subset_1(X2,sK0) )
   => ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
      & k1_xboole_0 != sK0
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ( k1_xboole_0 != X0
             => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ( k1_xboole_0 != X0
           => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).

fof(f108,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f105,f23])).

fof(f23,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f105,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK1,sK0) ),
    inference(resolution,[],[f76,f60])).

fof(f60,plain,(
    ~ r1_tarski(k2_tarski(sK1,sK2),sK0) ),
    inference(resolution,[],[f59,f39])).

fof(f39,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f59,plain,(
    ~ r2_hidden(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f58,f26])).

fof(f26,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f58,plain,
    ( ~ r2_hidden(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f29,f25])).

fof(f25,plain,(
    ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f76,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k2_tarski(X3,X4),X5)
      | ~ m1_subset_1(X4,X5)
      | v1_xboole_0(X5)
      | ~ m1_subset_1(X3,X5) ) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k2_tarski(X3,X4),X5)
      | ~ m1_subset_1(X4,X5)
      | v1_xboole_0(X5)
      | ~ m1_subset_1(X3,X5)
      | v1_xboole_0(X5) ) ),
    inference(resolution,[],[f66,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,X5)
      | r1_tarski(k2_tarski(X3,X4),X5)
      | ~ m1_subset_1(X4,X5)
      | v1_xboole_0(X5) ) ),
    inference(resolution,[],[f38,f28])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f42,plain,(
    ~ sQ4_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f24,f41])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:26:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (20413)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (20414)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (20413)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f42,f109,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(X0) | sQ4_eqProxy(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(equality_proxy_replacement,[],[f27,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    v1_xboole_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f108,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    m1_subset_1(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    (~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : (~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) => (? [X2] : (~m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X2] : (~m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(X2,sK0)) => (~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK2,sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : (~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : ((~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    v1_xboole_0(sK0) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f105,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    m1_subset_1(sK2,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,sK0) | v1_xboole_0(sK0) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.47    inference(resolution,[],[f76,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ~r1_tarski(k2_tarski(sK1,sK2),sK0)),
% 0.21/0.47    inference(resolution,[],[f59,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.47    inference(rectify,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ~r2_hidden(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f58,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ~r2_hidden(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(resolution,[],[f29,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (r1_tarski(k2_tarski(X3,X4),X5) | ~m1_subset_1(X4,X5) | v1_xboole_0(X5) | ~m1_subset_1(X3,X5)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (r1_tarski(k2_tarski(X3,X4),X5) | ~m1_subset_1(X4,X5) | v1_xboole_0(X5) | ~m1_subset_1(X3,X5) | v1_xboole_0(X5)) )),
% 0.21/0.47    inference(resolution,[],[f66,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (~r2_hidden(X3,X5) | r1_tarski(k2_tarski(X3,X4),X5) | ~m1_subset_1(X4,X5) | v1_xboole_0(X5)) )),
% 0.21/0.47    inference(resolution,[],[f38,f28])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.47    inference(nnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ~sQ4_eqProxy(k1_xboole_0,sK0)),
% 0.21/0.47    inference(equality_proxy_replacement,[],[f24,f41])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    k1_xboole_0 != sK0),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (20413)------------------------------
% 0.21/0.47  % (20413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (20413)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (20413)Memory used [KB]: 6140
% 0.21/0.47  % (20413)Time elapsed: 0.063 s
% 0.21/0.47  % (20413)------------------------------
% 0.21/0.47  % (20413)------------------------------
% 0.21/0.47  % (20407)Success in time 0.112 s
%------------------------------------------------------------------------------
