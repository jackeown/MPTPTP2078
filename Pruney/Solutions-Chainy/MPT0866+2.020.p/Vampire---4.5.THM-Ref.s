%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:45 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   43 (  69 expanded)
%              Number of leaves         :   10 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  117 ( 217 expanded)
%              Number of equality atoms :   49 ( 117 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f24,f25,f64,f22,f56,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( sQ3_eqProxy(k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)),X2)
      | sQ3_eqProxy(X0,X1)
      | ~ m1_subset_1(X2,X1)
      | ~ v1_xboole_0(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f85,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | sQ3_eqProxy(k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f26,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f85,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | ~ v1_xboole_0(X1)
      | sQ3_eqProxy(X1,X2)
      | ~ m1_subset_1(X3,X2) ) ),
    inference(resolution,[],[f42,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | sQ3_eqProxy(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f31,f34])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f56,plain,(
    ~ sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),sK2) ),
    inference(resolution,[],[f52,f35])).

fof(f35,plain,(
    ~ sQ3_eqProxy(sK2,k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))) ),
    inference(equality_proxy_replacement,[],[f23,f34])).

fof(f23,plain,(
    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
          & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
        & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
   => ( sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
      & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f34])).

fof(f22,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    ~ sQ3_eqProxy(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f59,f37])).

fof(f37,plain,(
    ~ sQ3_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f20,f34])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0] :
      ( sQ3_eqProxy(k1_xboole_0,X0)
      | ~ sQ3_eqProxy(k1_xboole_0,k2_zfmisc_1(X0,sK1)) ) ),
    inference(resolution,[],[f41,f36])).

fof(f36,plain,(
    ~ sQ3_eqProxy(k1_xboole_0,sK1) ),
    inference(equality_proxy_replacement,[],[f21,f34])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k1_xboole_0,X1)
      | sQ3_eqProxy(k1_xboole_0,X0)
      | ~ sQ3_eqProxy(k1_xboole_0,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f28,f34,f34,f34])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f25,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 13:37:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.40  % (32717)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.18/0.40  % (32717)Refutation found. Thanks to Tanya!
% 0.18/0.40  % SZS status Theorem for theBenchmark
% 0.18/0.41  % (32726)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.18/0.42  % SZS output start Proof for theBenchmark
% 0.18/0.42  fof(f189,plain,(
% 0.18/0.42    $false),
% 0.18/0.42    inference(unit_resulting_resolution,[],[f24,f25,f64,f22,f56,f125])).
% 0.18/0.42  fof(f125,plain,(
% 0.18/0.42    ( ! [X2,X0,X1] : (sQ3_eqProxy(k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)),X2) | sQ3_eqProxy(X0,X1) | ~m1_subset_1(X2,X1) | ~v1_xboole_0(X0) | ~v1_relat_1(X1)) )),
% 0.18/0.42    inference(resolution,[],[f85,f38])).
% 0.18/0.42  fof(f38,plain,(
% 0.18/0.42    ( ! [X0,X1] : (~r2_hidden(X0,X1) | sQ3_eqProxy(k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)),X0) | ~v1_relat_1(X1)) )),
% 0.18/0.42    inference(equality_proxy_replacement,[],[f26,f34])).
% 0.18/0.42  fof(f34,plain,(
% 0.18/0.42    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.18/0.42    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.18/0.42  fof(f26,plain,(
% 0.18/0.42    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f11])).
% 0.18/0.42  fof(f11,plain,(
% 0.18/0.42    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.18/0.42    inference(flattening,[],[f10])).
% 0.18/0.42  fof(f10,plain,(
% 0.18/0.42    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.18/0.42    inference(ennf_transformation,[],[f6])).
% 0.18/0.42  fof(f6,axiom,(
% 0.18/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.18/0.42  fof(f85,plain,(
% 0.18/0.42    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | ~v1_xboole_0(X1) | sQ3_eqProxy(X1,X2) | ~m1_subset_1(X3,X2)) )),
% 0.18/0.42    inference(resolution,[],[f42,f27])).
% 0.18/0.42  fof(f27,plain,(
% 0.18/0.42    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f13])).
% 0.18/0.42  fof(f13,plain,(
% 0.18/0.42    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.18/0.42    inference(flattening,[],[f12])).
% 0.18/0.42  fof(f12,plain,(
% 0.18/0.42    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.18/0.42    inference(ennf_transformation,[],[f4])).
% 0.18/0.42  fof(f4,axiom,(
% 0.18/0.42    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.18/0.42  fof(f42,plain,(
% 0.18/0.42    ( ! [X0,X1] : (~v1_xboole_0(X1) | sQ3_eqProxy(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.18/0.42    inference(equality_proxy_replacement,[],[f31,f34])).
% 0.18/0.42  fof(f31,plain,(
% 0.18/0.42    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f14])).
% 0.18/0.42  fof(f14,plain,(
% 0.18/0.42    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.18/0.42    inference(ennf_transformation,[],[f2])).
% 0.18/0.42  fof(f2,axiom,(
% 0.18/0.42    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.18/0.42  fof(f56,plain,(
% 0.18/0.42    ~sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),sK2)),
% 0.18/0.42    inference(resolution,[],[f52,f35])).
% 0.18/0.42  fof(f35,plain,(
% 0.18/0.42    ~sQ3_eqProxy(sK2,k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)))),
% 0.18/0.42    inference(equality_proxy_replacement,[],[f23,f34])).
% 0.18/0.42  fof(f23,plain,(
% 0.18/0.42    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.18/0.42    inference(cnf_transformation,[],[f17])).
% 0.18/0.42  fof(f17,plain,(
% 0.18/0.42    (sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.18/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f16,f15])).
% 0.18/0.42  fof(f15,plain,(
% 0.18/0.42    ? [X0,X1] : (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.18/0.42    introduced(choice_axiom,[])).
% 0.18/0.42  fof(f16,plain,(
% 0.18/0.42    ? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) => (sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.42    introduced(choice_axiom,[])).
% 0.18/0.42  fof(f9,plain,(
% 0.18/0.42    ? [X0,X1] : (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.18/0.42    inference(ennf_transformation,[],[f8])).
% 0.18/0.42  fof(f8,negated_conjecture,(
% 0.18/0.42    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.18/0.42    inference(negated_conjecture,[],[f7])).
% 0.18/0.42  fof(f7,conjecture,(
% 0.18/0.42    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).
% 0.18/0.42  fof(f52,plain,(
% 0.18/0.42    ( ! [X0,X1] : (sQ3_eqProxy(X1,X0) | ~sQ3_eqProxy(X0,X1)) )),
% 0.18/0.42    inference(equality_proxy_axiom,[],[f34])).
% 0.18/0.42  fof(f22,plain,(
% 0.18/0.42    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.18/0.42    inference(cnf_transformation,[],[f17])).
% 0.18/0.42  fof(f64,plain,(
% 0.18/0.42    ~sQ3_eqProxy(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 0.18/0.42    inference(resolution,[],[f59,f37])).
% 0.18/0.42  fof(f37,plain,(
% 0.18/0.42    ~sQ3_eqProxy(k1_xboole_0,sK0)),
% 0.18/0.42    inference(equality_proxy_replacement,[],[f20,f34])).
% 0.18/0.42  fof(f20,plain,(
% 0.18/0.42    k1_xboole_0 != sK0),
% 0.18/0.42    inference(cnf_transformation,[],[f17])).
% 0.18/0.42  fof(f59,plain,(
% 0.18/0.42    ( ! [X0] : (sQ3_eqProxy(k1_xboole_0,X0) | ~sQ3_eqProxy(k1_xboole_0,k2_zfmisc_1(X0,sK1))) )),
% 0.18/0.42    inference(resolution,[],[f41,f36])).
% 0.18/0.42  fof(f36,plain,(
% 0.18/0.42    ~sQ3_eqProxy(k1_xboole_0,sK1)),
% 0.18/0.42    inference(equality_proxy_replacement,[],[f21,f34])).
% 0.18/0.42  fof(f21,plain,(
% 0.18/0.42    k1_xboole_0 != sK1),
% 0.18/0.42    inference(cnf_transformation,[],[f17])).
% 0.18/0.42  fof(f41,plain,(
% 0.18/0.42    ( ! [X0,X1] : (sQ3_eqProxy(k1_xboole_0,X1) | sQ3_eqProxy(k1_xboole_0,X0) | ~sQ3_eqProxy(k1_xboole_0,k2_zfmisc_1(X0,X1))) )),
% 0.18/0.42    inference(equality_proxy_replacement,[],[f28,f34,f34,f34])).
% 0.18/0.42  fof(f28,plain,(
% 0.18/0.42    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f19])).
% 0.18/0.42  fof(f19,plain,(
% 0.18/0.42    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.18/0.42    inference(flattening,[],[f18])).
% 0.18/0.42  fof(f18,plain,(
% 0.18/0.42    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.18/0.42    inference(nnf_transformation,[],[f3])).
% 0.18/0.42  fof(f3,axiom,(
% 0.18/0.42    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.18/0.42  fof(f25,plain,(
% 0.18/0.42    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.18/0.42    inference(cnf_transformation,[],[f5])).
% 0.18/0.42  fof(f5,axiom,(
% 0.18/0.42    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.18/0.42  fof(f24,plain,(
% 0.18/0.42    v1_xboole_0(k1_xboole_0)),
% 0.18/0.42    inference(cnf_transformation,[],[f1])).
% 0.18/0.42  fof(f1,axiom,(
% 0.18/0.42    v1_xboole_0(k1_xboole_0)),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.18/0.42  % SZS output end Proof for theBenchmark
% 0.18/0.42  % (32717)------------------------------
% 0.18/0.42  % (32717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.42  % (32717)Termination reason: Refutation
% 0.18/0.42  
% 0.18/0.42  % (32717)Memory used [KB]: 6140
% 0.18/0.42  % (32717)Time elapsed: 0.030 s
% 0.18/0.42  % (32717)------------------------------
% 0.18/0.42  % (32717)------------------------------
% 0.18/0.42  % (32709)Success in time 0.08 s
%------------------------------------------------------------------------------
