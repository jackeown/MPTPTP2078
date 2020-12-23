%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  69 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :   17
%              Number of atoms          :  138 ( 212 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(subsumption_resolution,[],[f148,f21])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_relat_1)).

fof(f148,plain,(
    ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f144,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f144,plain,(
    ! [X0] :
      ( ~ r1_tarski(k8_relat_1(sK1,sK2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f141,f32])).

fof(f32,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
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

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f141,plain,(
    ! [X3] :
      ( ~ r2_hidden(k8_relat_1(sK1,sK2),k1_zfmisc_1(X3))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f131,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f131,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k8_relat_1(sK1,sK2),k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f130,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f130,plain,(
    ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f128,f45])).

fof(f45,plain,(
    ! [X0] : sQ4_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f128,plain,
    ( ~ sQ4_eqProxy(k8_relat_1(sK1,sK2),k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f126,f25])).

fof(f126,plain,(
    ! [X0] :
      ( ~ r1_tarski(k8_relat_1(sK0,k8_relat_1(sK1,sK2)),X0)
      | ~ sQ4_eqProxy(X0,k8_relat_1(sK1,sK2)) ) ),
    inference(resolution,[],[f102,f22])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(k8_relat_1(sK0,k8_relat_1(X0,sK2)),X1)
      | ~ sQ4_eqProxy(X1,k8_relat_1(sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f101,f21])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,X0)
      | ~ v1_relat_1(sK2)
      | ~ r1_tarski(k8_relat_1(sK0,k8_relat_1(X0,sK2)),X1)
      | ~ sQ4_eqProxy(X1,k8_relat_1(sK1,sK2)) ) ),
    inference(resolution,[],[f37,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ sQ4_eqProxy(X1,k8_relat_1(sK0,sK2))
      | ~ r1_tarski(X1,X0)
      | ~ sQ4_eqProxy(X0,k8_relat_1(sK1,sK2)) ) ),
    inference(resolution,[],[f42,f23])).

fof(f23,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | ~ sQ4_eqProxy(X2,X3)
      | ~ r1_tarski(X0,X2)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f34])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k8_relat_1(X0,k8_relat_1(X1,X2)),k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_proxy_replacement,[],[f31,f34])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:06:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (7532)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.46  % (7523)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (7523)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f149,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f148,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    v1_relat_1(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.46    inference(flattening,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1,X2] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))))),
% 0.21/0.46    inference(negated_conjecture,[],[f6])).
% 0.21/0.46  fof(f6,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_relat_1)).
% 0.21/0.46  fof(f148,plain,(
% 0.21/0.46    ~v1_relat_1(sK2)),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f146])).
% 0.21/0.46  fof(f146,plain,(
% 0.21/0.46    ~v1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.46    inference(resolution,[],[f144,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.21/0.46  fof(f144,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(k8_relat_1(sK1,sK2),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(resolution,[],[f141,f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.46    inference(rectify,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.46  fof(f141,plain,(
% 0.21/0.46    ( ! [X3] : (~r2_hidden(k8_relat_1(sK1,sK2),k1_zfmisc_1(X3)) | ~v1_relat_1(X3)) )),
% 0.21/0.46    inference(resolution,[],[f131,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_subset_1(k8_relat_1(sK1,sK2),k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(resolution,[],[f130,f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    ~v1_relat_1(k8_relat_1(sK1,sK2))),
% 0.21/0.46    inference(subsumption_resolution,[],[f128,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X0] : (sQ4_eqProxy(X0,X0)) )),
% 0.21/0.46    inference(equality_proxy_axiom,[],[f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.46    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.21/0.46  fof(f128,plain,(
% 0.21/0.46    ~sQ4_eqProxy(k8_relat_1(sK1,sK2),k8_relat_1(sK1,sK2)) | ~v1_relat_1(k8_relat_1(sK1,sK2))),
% 0.21/0.46    inference(resolution,[],[f126,f25])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(k8_relat_1(sK0,k8_relat_1(sK1,sK2)),X0) | ~sQ4_eqProxy(X0,k8_relat_1(sK1,sK2))) )),
% 0.21/0.46    inference(resolution,[],[f102,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    r1_tarski(sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(sK0,X0) | ~r1_tarski(k8_relat_1(sK0,k8_relat_1(X0,sK2)),X1) | ~sQ4_eqProxy(X1,k8_relat_1(sK1,sK2))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f101,f21])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(sK0,X0) | ~v1_relat_1(sK2) | ~r1_tarski(k8_relat_1(sK0,k8_relat_1(X0,sK2)),X1) | ~sQ4_eqProxy(X1,k8_relat_1(sK1,sK2))) )),
% 0.21/0.46    inference(resolution,[],[f37,f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~sQ4_eqProxy(X1,k8_relat_1(sK0,sK2)) | ~r1_tarski(X1,X0) | ~sQ4_eqProxy(X0,k8_relat_1(sK1,sK2))) )),
% 0.21/0.46    inference(resolution,[],[f42,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK2))),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (r1_tarski(X1,X3) | ~sQ4_eqProxy(X2,X3) | ~r1_tarski(X0,X2) | ~sQ4_eqProxy(X0,X1)) )),
% 0.21/0.46    inference(equality_proxy_axiom,[],[f34])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (sQ4_eqProxy(k8_relat_1(X0,k8_relat_1(X1,X2)),k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.46    inference(equality_proxy_replacement,[],[f31,f34])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(flattening,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (7523)------------------------------
% 0.21/0.46  % (7523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (7523)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (7523)Memory used [KB]: 6140
% 0.21/0.46  % (7523)Time elapsed: 0.057 s
% 0.21/0.46  % (7523)------------------------------
% 0.21/0.46  % (7523)------------------------------
% 0.21/0.46  % (7514)Success in time 0.108 s
%------------------------------------------------------------------------------
