%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:04 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 116 expanded)
%              Number of leaves         :   13 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  189 ( 415 expanded)
%              Number of equality atoms :   15 (  33 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f90,f105,f121,f137])).

fof(f137,plain,
    ( spl5_5
    | spl5_6
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f136,f38,f64,f61])).

fof(f61,plain,
    ( spl5_5
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f64,plain,
    ( spl5_6
  <=> ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f38,plain,
    ( spl5_1
  <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f124,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK1,sK0))
        | r2_hidden(X0,sK2) )
    | ~ spl5_1 ),
    inference(resolution,[],[f123,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f123,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK2,sK0))
        | ~ r2_hidden(X0,k2_zfmisc_1(sK1,sK0)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f39,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f121,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f26,f117])).

fof(f117,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_6 ),
    inference(resolution,[],[f108,f44])).

fof(f44,plain,(
    r2_hidden(sK4(sK1,sK2),sK1) ),
    inference(resolution,[],[f26,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f108,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK4(X2,sK2),sK1)
        | r1_tarski(X2,sK2) )
    | ~ spl5_6 ),
    inference(resolution,[],[f65,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f26,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(sK1,sK2)
    & ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
      | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 )
   => ( ~ r1_tarski(sK1,sK2)
      & ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
        | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X1,X2)
      & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ r1_tarski(X1,X2)
          & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
            | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f105,plain,
    ( spl5_5
    | spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f104,f41,f64,f61])).

fof(f41,plain,
    ( spl5_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f48,f36])).

fof(f48,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X3,sK2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f45,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK2))
        | ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f42,f31])).

fof(f42,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f90,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f24,f78])).

fof(f78,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_5 ),
    inference(resolution,[],[f71,f27])).

fof(f27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f71,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK0 = X0 )
    | ~ spl5_5 ),
    inference(resolution,[],[f68,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f68,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0,sK0),X0)
        | sK0 = X0 )
    | ~ spl5_5 ),
    inference(resolution,[],[f62,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f62,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f25,f41,f38])).

fof(f25,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
    | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:23:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.35  ipcrm: permission denied for id (807567360)
% 0.13/0.36  ipcrm: permission denied for id (807600134)
% 0.13/0.36  ipcrm: permission denied for id (807632904)
% 0.13/0.36  ipcrm: permission denied for id (807665675)
% 0.13/0.38  ipcrm: permission denied for id (807731230)
% 0.13/0.38  ipcrm: permission denied for id (807764005)
% 0.13/0.39  ipcrm: permission denied for id (807862318)
% 0.13/0.40  ipcrm: permission denied for id (807895090)
% 0.13/0.40  ipcrm: permission denied for id (807927860)
% 0.13/0.41  ipcrm: permission denied for id (808026173)
% 0.19/0.41  ipcrm: permission denied for id (808058949)
% 0.19/0.42  ipcrm: permission denied for id (808124494)
% 0.19/0.42  ipcrm: permission denied for id (808157263)
% 0.19/0.43  ipcrm: permission denied for id (808222809)
% 0.19/0.44  ipcrm: permission denied for id (808255582)
% 0.19/0.44  ipcrm: permission denied for id (808288354)
% 0.19/0.46  ipcrm: permission denied for id (808386677)
% 0.19/0.47  ipcrm: permission denied for id (808419452)
% 0.19/0.47  ipcrm: permission denied for id (808452222)
% 0.19/0.60  % (7450)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.61  % (7450)Refutation found. Thanks to Tanya!
% 0.19/0.61  % SZS status Theorem for theBenchmark
% 0.19/0.62  % SZS output start Proof for theBenchmark
% 0.19/0.62  fof(f138,plain,(
% 0.19/0.62    $false),
% 0.19/0.62    inference(avatar_sat_refutation,[],[f43,f90,f105,f121,f137])).
% 0.19/0.62  fof(f137,plain,(
% 0.19/0.62    spl5_5 | spl5_6 | ~spl5_1),
% 0.19/0.62    inference(avatar_split_clause,[],[f136,f38,f64,f61])).
% 0.19/0.62  fof(f61,plain,(
% 0.19/0.62    spl5_5 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 0.19/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.62  fof(f64,plain,(
% 0.19/0.62    spl5_6 <=> ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1))),
% 0.19/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.19/0.62  fof(f38,plain,(
% 0.19/0.62    spl5_1 <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))),
% 0.19/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.62  fof(f136,plain,(
% 0.19/0.62    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X1,sK0) | ~r2_hidden(X0,sK1)) ) | ~spl5_1),
% 0.19/0.62    inference(resolution,[],[f124,f36])).
% 0.19/0.62  fof(f36,plain,(
% 0.19/0.62    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.19/0.62    inference(cnf_transformation,[],[f23])).
% 0.19/0.62  fof(f23,plain,(
% 0.19/0.62    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.19/0.62    inference(flattening,[],[f22])).
% 0.19/0.62  fof(f22,plain,(
% 0.19/0.62    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.19/0.62    inference(nnf_transformation,[],[f5])).
% 0.19/0.62  fof(f5,axiom,(
% 0.19/0.62    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.19/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.19/0.62  fof(f124,plain,(
% 0.19/0.62    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK1,sK0)) | r2_hidden(X0,sK2)) ) | ~spl5_1),
% 0.19/0.62    inference(resolution,[],[f123,f34])).
% 0.19/0.62  fof(f34,plain,(
% 0.19/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.19/0.62    inference(cnf_transformation,[],[f23])).
% 0.19/0.62  fof(f123,plain,(
% 0.19/0.62    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK2,sK0)) | ~r2_hidden(X0,k2_zfmisc_1(sK1,sK0))) ) | ~spl5_1),
% 0.19/0.62    inference(resolution,[],[f39,f31])).
% 0.19/0.62  fof(f31,plain,(
% 0.19/0.62    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.19/0.62    inference(cnf_transformation,[],[f21])).
% 0.19/0.62  fof(f21,plain,(
% 0.19/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 0.19/0.62  fof(f20,plain,(
% 0.19/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.19/0.62    introduced(choice_axiom,[])).
% 0.19/0.62  fof(f19,plain,(
% 0.19/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.62    inference(rectify,[],[f18])).
% 0.19/0.62  fof(f18,plain,(
% 0.19/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.62    inference(nnf_transformation,[],[f12])).
% 0.19/0.62  fof(f12,plain,(
% 0.19/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.62    inference(ennf_transformation,[],[f2])).
% 0.19/0.62  fof(f2,axiom,(
% 0.19/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.62  fof(f39,plain,(
% 0.19/0.62    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)) | ~spl5_1),
% 0.19/0.62    inference(avatar_component_clause,[],[f38])).
% 0.19/0.62  fof(f121,plain,(
% 0.19/0.62    ~spl5_6),
% 0.19/0.62    inference(avatar_contradiction_clause,[],[f119])).
% 0.19/0.62  fof(f119,plain,(
% 0.19/0.62    $false | ~spl5_6),
% 0.19/0.62    inference(subsumption_resolution,[],[f26,f117])).
% 0.19/0.62  fof(f117,plain,(
% 0.19/0.62    r1_tarski(sK1,sK2) | ~spl5_6),
% 0.19/0.62    inference(resolution,[],[f108,f44])).
% 0.19/0.62  fof(f44,plain,(
% 0.19/0.62    r2_hidden(sK4(sK1,sK2),sK1)),
% 0.19/0.62    inference(resolution,[],[f26,f32])).
% 0.19/0.62  fof(f32,plain,(
% 0.19/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.19/0.62    inference(cnf_transformation,[],[f21])).
% 0.19/0.62  fof(f108,plain,(
% 0.19/0.62    ( ! [X2] : (~r2_hidden(sK4(X2,sK2),sK1) | r1_tarski(X2,sK2)) ) | ~spl5_6),
% 0.19/0.62    inference(resolution,[],[f65,f33])).
% 0.19/0.62  fof(f33,plain,(
% 0.19/0.62    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.19/0.62    inference(cnf_transformation,[],[f21])).
% 0.19/0.62  fof(f65,plain,(
% 0.19/0.62    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1)) ) | ~spl5_6),
% 0.19/0.62    inference(avatar_component_clause,[],[f64])).
% 0.19/0.62  fof(f26,plain,(
% 0.19/0.62    ~r1_tarski(sK1,sK2)),
% 0.19/0.62    inference(cnf_transformation,[],[f14])).
% 0.19/0.62  fof(f14,plain,(
% 0.19/0.62    ~r1_tarski(sK1,sK2) & (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))) & k1_xboole_0 != sK0),
% 0.19/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).
% 1.08/0.62  fof(f13,plain,(
% 1.08/0.62    ? [X0,X1,X2] : (~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0) => (~r1_tarski(sK1,sK2) & (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))) & k1_xboole_0 != sK0)),
% 1.08/0.62    introduced(choice_axiom,[])).
% 1.08/0.62  fof(f9,plain,(
% 1.08/0.62    ? [X0,X1,X2] : (~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 1.08/0.62    inference(ennf_transformation,[],[f7])).
% 1.08/0.62  fof(f7,negated_conjecture,(
% 1.08/0.62    ~! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 1.08/0.62    inference(negated_conjecture,[],[f6])).
% 1.08/0.62  fof(f6,conjecture,(
% 1.08/0.62    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 1.08/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 1.08/0.62  fof(f105,plain,(
% 1.08/0.62    spl5_5 | spl5_6 | ~spl5_2),
% 1.08/0.62    inference(avatar_split_clause,[],[f104,f41,f64,f61])).
% 1.08/0.62  fof(f41,plain,(
% 1.08/0.62    spl5_2 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))),
% 1.08/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.08/0.62  fof(f104,plain,(
% 1.08/0.62    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl5_2),
% 1.08/0.62    inference(resolution,[],[f48,f36])).
% 1.08/0.62  fof(f48,plain,(
% 1.08/0.62    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK2)) ) | ~spl5_2),
% 1.08/0.62    inference(resolution,[],[f45,f35])).
% 1.08/0.62  fof(f35,plain,(
% 1.08/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.08/0.62    inference(cnf_transformation,[],[f23])).
% 1.08/0.62  fof(f45,plain,(
% 1.08/0.62    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK2)) | ~r2_hidden(X0,k2_zfmisc_1(sK0,sK1))) ) | ~spl5_2),
% 1.08/0.62    inference(resolution,[],[f42,f31])).
% 1.08/0.62  fof(f42,plain,(
% 1.08/0.62    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) | ~spl5_2),
% 1.08/0.62    inference(avatar_component_clause,[],[f41])).
% 1.08/0.62  fof(f90,plain,(
% 1.08/0.62    ~spl5_5),
% 1.08/0.62    inference(avatar_contradiction_clause,[],[f79])).
% 1.08/0.62  fof(f79,plain,(
% 1.08/0.62    $false | ~spl5_5),
% 1.08/0.62    inference(subsumption_resolution,[],[f24,f78])).
% 1.08/0.62  fof(f78,plain,(
% 1.08/0.62    k1_xboole_0 = sK0 | ~spl5_5),
% 1.08/0.62    inference(resolution,[],[f71,f27])).
% 1.08/0.62  fof(f27,plain,(
% 1.08/0.62    v1_xboole_0(k1_xboole_0)),
% 1.08/0.62    inference(cnf_transformation,[],[f3])).
% 1.08/0.62  fof(f3,axiom,(
% 1.08/0.62    v1_xboole_0(k1_xboole_0)),
% 1.08/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.08/0.62  fof(f71,plain,(
% 1.08/0.62    ( ! [X0] : (~v1_xboole_0(X0) | sK0 = X0) ) | ~spl5_5),
% 1.08/0.62    inference(resolution,[],[f68,f28])).
% 1.08/0.62  fof(f28,plain,(
% 1.08/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.08/0.62    inference(cnf_transformation,[],[f10])).
% 1.08/0.62  fof(f10,plain,(
% 1.08/0.62    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.08/0.62    inference(ennf_transformation,[],[f8])).
% 1.08/0.62  fof(f8,plain,(
% 1.08/0.62    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.08/0.62    inference(unused_predicate_definition_removal,[],[f1])).
% 1.08/0.62  fof(f1,axiom,(
% 1.08/0.62    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.08/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.08/0.62  fof(f68,plain,(
% 1.08/0.62    ( ! [X0] : (r2_hidden(sK3(X0,sK0),X0) | sK0 = X0) ) | ~spl5_5),
% 1.08/0.62    inference(resolution,[],[f62,f29])).
% 1.08/0.62  fof(f29,plain,(
% 1.08/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0) | X0 = X1) )),
% 1.08/0.62    inference(cnf_transformation,[],[f17])).
% 1.08/0.62  fof(f17,plain,(
% 1.08/0.62    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 1.08/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 1.08/0.62  fof(f16,plain,(
% 1.08/0.62    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 1.08/0.62    introduced(choice_axiom,[])).
% 1.08/0.62  fof(f15,plain,(
% 1.08/0.62    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.08/0.62    inference(nnf_transformation,[],[f11])).
% 1.08/0.62  fof(f11,plain,(
% 1.08/0.62    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.08/0.62    inference(ennf_transformation,[],[f4])).
% 1.08/0.62  fof(f4,axiom,(
% 1.08/0.62    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.08/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 1.08/0.62  fof(f62,plain,(
% 1.08/0.62    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl5_5),
% 1.08/0.62    inference(avatar_component_clause,[],[f61])).
% 1.08/0.62  fof(f24,plain,(
% 1.08/0.62    k1_xboole_0 != sK0),
% 1.08/0.62    inference(cnf_transformation,[],[f14])).
% 1.08/0.62  fof(f43,plain,(
% 1.08/0.62    spl5_1 | spl5_2),
% 1.08/0.62    inference(avatar_split_clause,[],[f25,f41,f38])).
% 1.08/0.62  fof(f25,plain,(
% 1.08/0.62    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))),
% 1.08/0.62    inference(cnf_transformation,[],[f14])).
% 1.08/0.62  % SZS output end Proof for theBenchmark
% 1.08/0.62  % (7450)------------------------------
% 1.08/0.62  % (7450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.08/0.62  % (7450)Termination reason: Refutation
% 1.08/0.62  
% 1.08/0.62  % (7450)Memory used [KB]: 10746
% 1.08/0.62  % (7450)Time elapsed: 0.097 s
% 1.08/0.62  % (7450)------------------------------
% 1.08/0.62  % (7450)------------------------------
% 1.08/0.63  % (7311)Success in time 0.278 s
%------------------------------------------------------------------------------
