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
% DateTime   : Thu Dec  3 12:42:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 223 expanded)
%              Number of leaves         :    9 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  129 ( 619 expanded)
%              Number of equality atoms :   19 (  84 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f396,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f222,f395])).

fof(f395,plain,(
    spl11_2 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f27,f348,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f348,plain,
    ( r2_hidden(sK9(k1_xboole_0,sK1),k1_xboole_0)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f259,f346,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | r2_hidden(sK9(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f346,plain,
    ( k1_xboole_0 != sK1
    | spl11_2 ),
    inference(superposition,[],[f16,f273])).

fof(f273,plain,
    ( ! [X0] : sK1 = k2_zfmisc_1(X0,sK1)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f259,f259,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f16,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f259,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f224,f242,f36])).

fof(f36,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f242,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK10(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1))
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f15,f233,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f233,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(sK10(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f225,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f225,plain,
    ( ~ r2_hidden(sK10(sK0,sK2),sK2)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f47,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl11_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f15,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f224,plain,
    ( r2_hidden(sK10(sK0,sK2),sK0)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f47,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK10(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f222,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f27,f165,f34])).

fof(f165,plain,
    ( r2_hidden(sK9(k1_xboole_0,sK0),k1_xboole_0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f82,f158,f25])).

fof(f158,plain,
    ( k1_xboole_0 != sK0
    | spl11_1 ),
    inference(superposition,[],[f16,f95])).

fof(f95,plain,
    ( ! [X0] : sK0 = k2_zfmisc_1(sK0,X0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f82,f82,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f82,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f49,f77,f36])).

fof(f77,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK10(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f15,f58,f28])).

fof(f58,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,sK10(sK1,sK3)),k2_zfmisc_1(X1,sK3))
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f50,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,
    ( ~ r2_hidden(sK10(sK1,sK3),sK3)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f43,f30])).

fof(f43,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl11_1
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f49,plain,
    ( r2_hidden(sK10(sK1,sK3),sK1)
    | spl11_1 ),
    inference(unit_resulting_resolution,[],[f43,f29])).

fof(f48,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f14,f45,f41])).

fof(f14,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:17:07 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.19/0.44  % (10923)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.45  % (10923)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.46  % (10931)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f396,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(avatar_sat_refutation,[],[f48,f222,f395])).
% 0.19/0.46  fof(f395,plain,(
% 0.19/0.46    spl11_2),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f384])).
% 0.19/0.46  fof(f384,plain,(
% 0.19/0.46    $false | spl11_2),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f27,f348,f34])).
% 0.19/0.46  fof(f34,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f13])).
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.19/0.46    inference(ennf_transformation,[],[f6])).
% 0.19/0.46  fof(f6,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.19/0.46  fof(f348,plain,(
% 0.19/0.46    r2_hidden(sK9(k1_xboole_0,sK1),k1_xboole_0) | spl11_2),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f259,f346,f25])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X1) | r2_hidden(sK9(X0,X1),X0) | X0 = X1) )),
% 0.19/0.46    inference(cnf_transformation,[],[f11])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.19/0.46  fof(f346,plain,(
% 0.19/0.46    k1_xboole_0 != sK1 | spl11_2),
% 0.19/0.46    inference(superposition,[],[f16,f273])).
% 0.19/0.46  fof(f273,plain,(
% 0.19/0.46    ( ! [X0] : (sK1 = k2_zfmisc_1(X0,sK1)) ) | spl11_2),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f259,f259,f19])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 0.19/0.46    inference(cnf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.19/0.46    inference(cnf_transformation,[],[f10])).
% 0.19/0.46  fof(f10,plain,(
% 0.19/0.46    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.19/0.46    inference(flattening,[],[f9])).
% 0.19/0.46  fof(f9,plain,(
% 0.19/0.46    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.19/0.46    inference(ennf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,negated_conjecture,(
% 0.19/0.46    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.19/0.46    inference(negated_conjecture,[],[f7])).
% 0.19/0.46  fof(f7,conjecture,(
% 0.19/0.46    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.19/0.46  fof(f259,plain,(
% 0.19/0.46    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | spl11_2),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f224,f242,f36])).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 0.19/0.46    inference(equality_resolution,[],[f35])).
% 0.19/0.46  fof(f35,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.19/0.46    inference(equality_resolution,[],[f24])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.19/0.46    inference(cnf_transformation,[],[f4])).
% 0.19/0.46  fof(f242,plain,(
% 0.19/0.46    ( ! [X0] : (~r2_hidden(k4_tarski(sK10(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1))) ) | spl11_2),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f15,f233,f28])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f12])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.46  fof(f233,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK10(sK0,sK2),X0),k2_zfmisc_1(sK2,X1))) ) | spl11_2),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f225,f31])).
% 0.19/0.46  fof(f31,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.19/0.46  fof(f225,plain,(
% 0.19/0.46    ~r2_hidden(sK10(sK0,sK2),sK2) | spl11_2),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f47,f30])).
% 0.19/0.46  fof(f30,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r2_hidden(sK10(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f12])).
% 0.19/0.46  fof(f47,plain,(
% 0.19/0.46    ~r1_tarski(sK0,sK2) | spl11_2),
% 0.19/0.46    inference(avatar_component_clause,[],[f45])).
% 0.19/0.46  fof(f45,plain,(
% 0.19/0.46    spl11_2 <=> r1_tarski(sK0,sK2)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.19/0.46    inference(cnf_transformation,[],[f10])).
% 0.19/0.46  fof(f224,plain,(
% 0.19/0.46    r2_hidden(sK10(sK0,sK2),sK0) | spl11_2),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f47,f29])).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK10(X0,X1),X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f12])).
% 0.19/0.46  fof(f27,plain,(
% 0.19/0.46    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.19/0.46  fof(f222,plain,(
% 0.19/0.46    spl11_1),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f211])).
% 0.19/0.46  fof(f211,plain,(
% 0.19/0.46    $false | spl11_1),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f27,f165,f34])).
% 0.19/0.46  fof(f165,plain,(
% 0.19/0.46    r2_hidden(sK9(k1_xboole_0,sK0),k1_xboole_0) | spl11_1),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f82,f158,f25])).
% 0.19/0.46  fof(f158,plain,(
% 0.19/0.46    k1_xboole_0 != sK0 | spl11_1),
% 0.19/0.46    inference(superposition,[],[f16,f95])).
% 0.19/0.46  fof(f95,plain,(
% 0.19/0.46    ( ! [X0] : (sK0 = k2_zfmisc_1(sK0,X0)) ) | spl11_1),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f82,f82,f18])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 0.19/0.46    inference(cnf_transformation,[],[f4])).
% 0.19/0.46  fof(f82,plain,(
% 0.19/0.46    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | spl11_1),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f49,f77,f36])).
% 0.19/0.46  fof(f77,plain,(
% 0.19/0.46    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK10(sK1,sK3)),k2_zfmisc_1(sK0,sK1))) ) | spl11_1),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f15,f58,f28])).
% 0.19/0.46  fof(f58,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK10(sK1,sK3)),k2_zfmisc_1(X1,sK3))) ) | spl11_1),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f50,f32])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f5])).
% 0.19/0.46  fof(f50,plain,(
% 0.19/0.46    ~r2_hidden(sK10(sK1,sK3),sK3) | spl11_1),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f43,f30])).
% 0.19/0.46  fof(f43,plain,(
% 0.19/0.46    ~r1_tarski(sK1,sK3) | spl11_1),
% 0.19/0.46    inference(avatar_component_clause,[],[f41])).
% 0.19/0.46  fof(f41,plain,(
% 0.19/0.46    spl11_1 <=> r1_tarski(sK1,sK3)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.19/0.46  fof(f49,plain,(
% 0.19/0.46    r2_hidden(sK10(sK1,sK3),sK1) | spl11_1),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f43,f29])).
% 0.19/0.46  fof(f48,plain,(
% 0.19/0.46    ~spl11_1 | ~spl11_2),
% 0.19/0.46    inference(avatar_split_clause,[],[f14,f45,f41])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK1,sK3)),
% 0.19/0.46    inference(cnf_transformation,[],[f10])).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (10923)------------------------------
% 0.19/0.46  % (10923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (10923)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (10947)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.47  % (10923)Memory used [KB]: 6396
% 0.19/0.47  % (10923)Time elapsed: 0.093 s
% 0.19/0.47  % (10923)------------------------------
% 0.19/0.47  % (10923)------------------------------
% 0.19/0.47  % (10918)Success in time 0.132 s
%------------------------------------------------------------------------------
