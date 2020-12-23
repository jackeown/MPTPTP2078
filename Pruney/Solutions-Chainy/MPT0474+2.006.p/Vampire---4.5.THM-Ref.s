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
% DateTime   : Thu Dec  3 12:48:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  51 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :  126 ( 161 expanded)
%              Number of equality atoms :   37 (  56 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f39,f54])).

fof(f54,plain,
    ( ~ spl2_2
    | spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f51,f37,f33,f37])).

fof(f33,plain,
    ( spl2_1
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f37,plain,
    ( spl2_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f51,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl2_2 ),
    inference(resolution,[],[f50,f40])).

fof(f40,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f24,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f24,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f50,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK1(X0,k1_xboole_0),sK0(X0,k1_xboole_0)),X0)
        | k1_xboole_0 = k4_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f49,f40])).

fof(f49,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK0(X0,k1_xboole_0),sK1(X0,k1_xboole_0)),k1_xboole_0)
        | r2_hidden(k4_tarski(sK1(X0,k1_xboole_0),sK0(X0,k1_xboole_0)),X0)
        | k1_xboole_0 = k4_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f47,f38])).

fof(f38,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | k4_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f45,f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | k4_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f22,f19])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | k4_relat_1(X0) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,(
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

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(f39,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f37])).

fof(f18,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f35,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f7])).

fof(f7,negated_conjecture,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (23351)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.46  % (23351)Refutation not found, incomplete strategy% (23351)------------------------------
% 0.21/0.46  % (23351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (23351)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (23351)Memory used [KB]: 1535
% 0.21/0.46  % (23351)Time elapsed: 0.004 s
% 0.21/0.46  % (23351)------------------------------
% 0.21/0.46  % (23351)------------------------------
% 0.21/0.46  % (23343)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (23352)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (23344)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (23344)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f35,f39,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ~spl2_2 | spl2_1 | ~spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f51,f37,f33,f37])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    spl2_1 <=> k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    spl2_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | ~spl2_2),
% 0.21/0.47    inference(resolution,[],[f50,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(superposition,[],[f24,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(k4_tarski(sK1(X0,k1_xboole_0),sK0(X0,k1_xboole_0)),X0) | k1_xboole_0 = k4_relat_1(X0) | ~v1_xboole_0(X0)) ) | ~spl2_2),
% 0.21/0.47    inference(resolution,[],[f49,f40])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(k4_tarski(sK0(X0,k1_xboole_0),sK1(X0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK1(X0,k1_xboole_0),sK0(X0,k1_xboole_0)),X0) | k1_xboole_0 = k4_relat_1(X0) | ~v1_xboole_0(X0)) ) | ~spl2_2),
% 0.21/0.47    inference(resolution,[],[f47,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f37])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_xboole_0(X1) | k4_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.47    inference(resolution,[],[f45,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) | k4_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | ~v1_xboole_0(X1)) )),
% 0.21/0.47    inference(resolution,[],[f22,f19])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) | k4_relat_1(X0) = X1 | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ((~r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(rectify,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X3,X2),X0)) & (r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f18,f37])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ~spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f17,f33])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(flattening,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (23344)------------------------------
% 0.21/0.47  % (23344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (23344)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (23344)Memory used [KB]: 10618
% 0.21/0.47  % (23344)Time elapsed: 0.061 s
% 0.21/0.47  % (23344)------------------------------
% 0.21/0.47  % (23344)------------------------------
% 0.21/0.47  % (23340)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (23337)Success in time 0.123 s
%------------------------------------------------------------------------------
