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
% DateTime   : Thu Dec  3 12:51:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 (  94 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  188 ( 350 expanded)
%              Number of equality atoms :   64 ( 129 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f469,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f58,f68,f90,f120,f467])).

fof(f467,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f463])).

fof(f463,plain,
    ( $false
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f13,f462])).

fof(f462,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f445,f430])).

fof(f430,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f344,f168])).

fof(f168,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f18,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f18,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f344,plain,
    ( ! [X30] :
        ( r2_hidden(sK2(sK0,X30),X30)
        | k1_relat_1(sK0) = X30 )
    | ~ spl6_5 ),
    inference(resolution,[],[f21,f86])).

fof(f86,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl6_5
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f445,plain,
    ( sK0 = k1_relat_1(sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f344,f86])).

fof(f13,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(f120,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f13,f93])).

fof(f93,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl6_6 ),
    inference(resolution,[],[f91,f27])).

fof(f27,plain,(
    ! [X0,X1] : v1_relat_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f91,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK5(sK0,X0))
        | k1_xboole_0 = X0 )
    | ~ spl6_6 ),
    inference(resolution,[],[f89,f28])).

fof(f28,plain,(
    ! [X0,X1] : v1_funct_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f89,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK5(sK0,X1))
        | k1_xboole_0 = X1
        | ~ v1_relat_1(sK5(sK0,X1)) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_6
  <=> ! [X1] :
        ( k1_xboole_0 = X1
        | ~ v1_funct_1(sK5(sK0,X1))
        | ~ v1_relat_1(sK5(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f90,plain,
    ( spl6_5
    | spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f81,f66,f88,f85])).

fof(f66,plain,
    ( spl6_4
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(sK5(X0,X1))
        | sK5(X0,X1) = sK1(sK0)
        | ~ v1_relat_1(sK5(X0,X1))
        | sK0 != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X1
        | ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK5(sK0,X1))
        | ~ v1_funct_1(sK5(sK0,X1)) )
    | ~ spl6_4 ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X1
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK5(sK0,X1))
        | ~ v1_funct_1(sK5(sK0,X1)) )
    | ~ spl6_4 ),
    inference(superposition,[],[f14,f70])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK1(sK0),X1) = X0
        | ~ r2_hidden(X1,sK0)
        | ~ v1_relat_1(sK5(sK0,X0))
        | ~ v1_funct_1(sK5(sK0,X0)) )
    | ~ spl6_4 ),
    inference(superposition,[],[f26,f69])).

fof(f69,plain,
    ( ! [X0] :
        ( sK1(sK0) = sK5(sK0,X0)
        | ~ v1_relat_1(sK5(sK0,X0))
        | ~ v1_funct_1(sK5(sK0,X0)) )
    | ~ spl6_4 ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( sK0 != X0
        | sK5(X0,X1) = sK1(sK0)
        | ~ v1_relat_1(sK5(X0,X1))
        | ~ v1_funct_1(sK5(X0,X1)) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK5(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | k1_xboole_0 = k1_funct_1(sK1(X0),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f68,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_4 ),
    inference(avatar_split_clause,[],[f64,f66,f48,f44])).

fof(f44,plain,
    ( spl6_1
  <=> v1_funct_1(sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f48,plain,
    ( spl6_2
  <=> v1_relat_1(sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK5(X0,X1))
      | ~ v1_relat_1(sK1(sK0))
      | ~ v1_funct_1(sK1(sK0))
      | sK0 != X0
      | ~ v1_relat_1(sK5(X0,X1))
      | sK5(X0,X1) = sK1(sK0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X10,X11,X9] :
      ( sK0 != X11
      | ~ v1_funct_1(sK5(X9,X10))
      | ~ v1_relat_1(sK1(X11))
      | ~ v1_funct_1(sK1(X11))
      | sK0 != X9
      | ~ v1_relat_1(sK5(X9,X10))
      | sK5(X9,X10) = sK1(X11) ) ),
    inference(superposition,[],[f34,f29])).

fof(f29,plain,(
    ! [X0,X1] : k1_relat_1(sK5(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK1(X0))
      | ~ v1_funct_1(sK1(X0))
      | sK0 != X0
      | ~ v1_relat_1(X1)
      | sK1(X0) = X1 ) ),
    inference(superposition,[],[f12,f17])).

fof(f17,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f12,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f58,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f57])).

fof(f57,plain,
    ( $false
    | spl6_2 ),
    inference(resolution,[],[f50,f15])).

fof(f15,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,
    ( ~ v1_relat_1(sK1(sK0))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f56,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f55])).

fof(f55,plain,
    ( $false
    | spl6_1 ),
    inference(resolution,[],[f46,f16])).

fof(f16,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,
    ( ~ v1_funct_1(sK1(sK0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (30567)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (30574)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.47  % (30574)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (30567)Refutation not found, incomplete strategy% (30567)------------------------------
% 0.21/0.47  % (30567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (30567)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (30567)Memory used [KB]: 6012
% 0.21/0.47  % (30567)Time elapsed: 0.063 s
% 0.21/0.47  % (30567)------------------------------
% 0.21/0.47  % (30567)------------------------------
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f469,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f56,f58,f68,f90,f120,f467])).
% 0.21/0.47  fof(f467,plain,(
% 0.21/0.47    ~spl6_5),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f463])).
% 0.21/0.47  fof(f463,plain,(
% 0.21/0.47    $false | ~spl6_5),
% 0.21/0.47    inference(subsumption_resolution,[],[f13,f462])).
% 0.21/0.47  fof(f462,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | ~spl6_5),
% 0.21/0.47    inference(forward_demodulation,[],[f445,f430])).
% 0.21/0.47  fof(f430,plain,(
% 0.21/0.47    k1_xboole_0 = k1_relat_1(sK0) | ~spl6_5),
% 0.21/0.47    inference(resolution,[],[f344,f168])).
% 0.21/0.47  fof(f168,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(superposition,[],[f18,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.48  fof(f344,plain,(
% 0.21/0.48    ( ! [X30] : (r2_hidden(sK2(sK0,X30),X30) | k1_relat_1(sK0) = X30) ) | ~spl6_5),
% 0.21/0.48    inference(resolution,[],[f21,f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl6_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl6_5 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.48  fof(f445,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK0) | ~spl6_5),
% 0.21/0.48    inference(resolution,[],[f344,f86])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    k1_xboole_0 != sK0),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ~spl6_6),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    $false | ~spl6_6),
% 0.21/0.48    inference(subsumption_resolution,[],[f13,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl6_6),
% 0.21/0.48    inference(resolution,[],[f91,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(sK5(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(sK5(sK0,X0)) | k1_xboole_0 = X0) ) | ~spl6_6),
% 0.21/0.48    inference(resolution,[],[f89,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X1] : (~v1_funct_1(sK5(sK0,X1)) | k1_xboole_0 = X1 | ~v1_relat_1(sK5(sK0,X1))) ) | ~spl6_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl6_6 <=> ! [X1] : (k1_xboole_0 = X1 | ~v1_funct_1(sK5(sK0,X1)) | ~v1_relat_1(sK5(sK0,X1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl6_5 | spl6_6 | ~spl6_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f81,f66,f88,f85])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl6_4 <=> ! [X1,X0] : (~v1_funct_1(sK5(X0,X1)) | sK5(X0,X1) = sK1(sK0) | ~v1_relat_1(sK5(X0,X1)) | sK0 != X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r2_hidden(X0,sK0) | ~v1_relat_1(sK5(sK0,X1)) | ~v1_funct_1(sK5(sK0,X1))) ) | ~spl6_4),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK0) | ~v1_relat_1(sK5(sK0,X1)) | ~v1_funct_1(sK5(sK0,X1))) ) | ~spl6_4),
% 0.21/0.48    inference(superposition,[],[f14,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_funct_1(sK1(sK0),X1) = X0 | ~r2_hidden(X1,sK0) | ~v1_relat_1(sK5(sK0,X0)) | ~v1_funct_1(sK5(sK0,X0))) ) | ~spl6_4),
% 0.21/0.48    inference(superposition,[],[f26,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X0] : (sK1(sK0) = sK5(sK0,X0) | ~v1_relat_1(sK5(sK0,X0)) | ~v1_funct_1(sK5(sK0,X0))) ) | ~spl6_4),
% 0.21/0.48    inference(equality_resolution,[],[f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sK0 != X0 | sK5(X0,X1) = sK1(sK0) | ~v1_relat_1(sK5(X0,X1)) | ~v1_funct_1(sK5(X0,X1))) ) | ~spl6_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f66])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK5(X0,X1),X3) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | k1_xboole_0 = k1_funct_1(sK1(X0),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ~spl6_1 | ~spl6_2 | spl6_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f64,f66,f48,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl6_1 <=> v1_funct_1(sK1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl6_2 <=> v1_relat_1(sK1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_1(sK5(X0,X1)) | ~v1_relat_1(sK1(sK0)) | ~v1_funct_1(sK1(sK0)) | sK0 != X0 | ~v1_relat_1(sK5(X0,X1)) | sK5(X0,X1) = sK1(sK0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X10,X11,X9] : (sK0 != X11 | ~v1_funct_1(sK5(X9,X10)) | ~v1_relat_1(sK1(X11)) | ~v1_funct_1(sK1(X11)) | sK0 != X9 | ~v1_relat_1(sK5(X9,X10)) | sK5(X9,X10) = sK1(X11)) )),
% 0.21/0.48    inference(superposition,[],[f34,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_relat_1(sK5(X0,X1)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_relat_1(X1) != sK0 | ~v1_funct_1(X1) | ~v1_relat_1(sK1(X0)) | ~v1_funct_1(sK1(X0)) | sK0 != X0 | ~v1_relat_1(X1) | sK1(X0) = X1) )),
% 0.21/0.48    inference(superposition,[],[f12,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k1_relat_1(X2) != sK0 | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X1) != sK0 | ~v1_relat_1(X1) | X1 = X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl6_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    $false | spl6_2),
% 0.21/0.48    inference(resolution,[],[f50,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ~v1_relat_1(sK1(sK0)) | spl6_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f48])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl6_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    $false | spl6_1),
% 0.21/0.48    inference(resolution,[],[f46,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ~v1_funct_1(sK1(sK0)) | spl6_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f44])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (30574)------------------------------
% 0.21/0.48  % (30574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30574)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (30574)Memory used [KB]: 10874
% 0.21/0.48  % (30574)Time elapsed: 0.067 s
% 0.21/0.48  % (30574)------------------------------
% 0.21/0.48  % (30574)------------------------------
% 0.21/0.48  % (30553)Success in time 0.123 s
%------------------------------------------------------------------------------
