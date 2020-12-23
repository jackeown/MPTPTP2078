%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 176 expanded)
%              Number of leaves         :   14 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  219 ( 546 expanded)
%              Number of equality atoms :   72 ( 216 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f83,f95,f99,f121,f164,f253])).

fof(f253,plain,
    ( spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f170,f247])).

fof(f247,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | spl8_2
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f242,f225])).

fof(f225,plain,
    ( k1_funct_1(sK1,sK0) = sK6(k2_relat_1(sK1),k1_funct_1(sK1,sK0))
    | spl8_2
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f221,f218])).

fof(f218,plain,
    ( sK0 = sK3(sK1,sK6(k2_relat_1(sK1),k1_funct_1(sK1,sK0)))
    | spl8_2
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f186,f100])).

fof(f100,plain,
    ( ! [X0] :
        ( sK0 = sK3(sK1,X0)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl8_6 ),
    inference(resolution,[],[f94,f44])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f94,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK1,X1),k1_tarski(sK0))
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl8_6
  <=> ! [X1] :
        ( r2_hidden(sK3(sK1,X1),k1_tarski(sK0))
        | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f186,plain,
    ( r2_hidden(sK6(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f60,f22,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f22,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f60,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl8_2
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f221,plain,
    ( sK6(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = k1_funct_1(sK1,sK3(sK1,sK6(k2_relat_1(sK1),k1_funct_1(sK1,sK0))))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f20,f19,f186,f42])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f20,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f242,plain,
    ( ~ r2_hidden(sK6(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1))
    | spl8_2
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f187,f109])).

fof(f109,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK1))
        | k1_funct_1(sK1,sK0) = X1 )
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK0) = X1
        | ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(superposition,[],[f82,f100])).

fof(f82,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK3(sK1,X1)) = X1
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl8_4
  <=> ! [X1] :
        ( k1_funct_1(sK1,sK3(sK1,X1)) = X1
        | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f187,plain,
    ( k1_funct_1(sK1,sK0) != sK6(k2_relat_1(sK1),k1_funct_1(sK1,sK0))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f60,f22,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f170,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | spl8_2
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f167,f120])).

fof(f120,plain,
    ( k1_funct_1(sK1,sK0) = sK7(k2_relat_1(sK1))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl8_8
  <=> k1_funct_1(sK1,sK0) = sK7(k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f167,plain,
    ( r2_hidden(sK7(k2_relat_1(sK1)),k2_relat_1(sK1))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f60,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f164,plain,(
    ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f38,f154,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f154,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl8_2 ),
    inference(superposition,[],[f46,f140])).

fof(f140,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f21,f136])).

fof(f136,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f19,f61,f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f61,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f21,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f121,plain,
    ( spl8_2
    | spl8_8
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f115,f93,f81,f118,f59])).

fof(f115,plain,
    ( k1_funct_1(sK1,sK0) = sK7(k2_relat_1(sK1))
    | k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(resolution,[],[f109,f37])).

fof(f99,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | spl8_5 ),
    inference(unit_resulting_resolution,[],[f20,f91])).

fof(f91,plain,
    ( ~ v1_funct_1(sK1)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl8_5
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f95,plain,
    ( ~ spl8_1
    | ~ spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f51,f93,f89,f55])).

fof(f55,plain,
    ( spl8_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f51,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK1,X1),k1_tarski(sK0))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f43,f21])).

fof(f43,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f83,plain,
    ( spl8_4
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f48,f55,f81])).

fof(f48,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,sK3(sK1,X1)) = X1
      | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f20,f42])).

fof(f70,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f19,f57])).

fof(f57,plain,
    ( ~ v1_relat_1(sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (5158)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.46  % (5161)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.48  % (5181)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.49  % (5157)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.49  % (5179)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (5171)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.50  % (5170)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.50  % (5165)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.50  % (5178)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (5178)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f256,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f70,f83,f95,f99,f121,f164,f253])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    spl8_2 | ~spl8_4 | ~spl8_6 | ~spl8_8),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f248])).
% 0.21/0.51  fof(f248,plain,(
% 0.21/0.51    $false | (spl8_2 | ~spl8_4 | ~spl8_6 | ~spl8_8)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f170,f247])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | (spl8_2 | ~spl8_4 | ~spl8_6)),
% 0.21/0.51    inference(forward_demodulation,[],[f242,f225])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    k1_funct_1(sK1,sK0) = sK6(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) | (spl8_2 | ~spl8_6)),
% 0.21/0.51    inference(backward_demodulation,[],[f221,f218])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    sK0 = sK3(sK1,sK6(k2_relat_1(sK1),k1_funct_1(sK1,sK0))) | (spl8_2 | ~spl8_6)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f186,f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X0] : (sK0 = sK3(sK1,X0) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl8_6),
% 0.21/0.51    inference(resolution,[],[f94,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 0.21/0.51    inference(equality_resolution,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X1] : (r2_hidden(sK3(sK1,X1),k1_tarski(sK0)) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | ~spl8_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl8_6 <=> ! [X1] : (r2_hidden(sK3(sK1,X1),k1_tarski(sK0)) | ~r2_hidden(X1,k2_relat_1(sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    r2_hidden(sK6(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1)) | spl8_2),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f60,f22,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    k1_xboole_0 != k2_relat_1(sK1) | spl8_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    spl8_2 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    sK6(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = k1_funct_1(sK1,sK3(sK1,sK6(k2_relat_1(sK1),k1_funct_1(sK1,sK0)))) | spl8_2),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f20,f19,f186,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.51    inference(equality_resolution,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    v1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    v1_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    ~r2_hidden(sK6(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1)) | (spl8_2 | ~spl8_4 | ~spl8_6)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f187,f109])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | k1_funct_1(sK1,sK0) = X1) ) | (~spl8_4 | ~spl8_6)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f106])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ( ! [X1] : (k1_funct_1(sK1,sK0) = X1 | ~r2_hidden(X1,k2_relat_1(sK1)) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | (~spl8_4 | ~spl8_6)),
% 0.21/0.51    inference(superposition,[],[f82,f100])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X1] : (k1_funct_1(sK1,sK3(sK1,X1)) = X1 | ~r2_hidden(X1,k2_relat_1(sK1))) ) | ~spl8_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    spl8_4 <=> ! [X1] : (k1_funct_1(sK1,sK3(sK1,X1)) = X1 | ~r2_hidden(X1,k2_relat_1(sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    k1_funct_1(sK1,sK0) != sK6(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) | spl8_2),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f60,f22,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sK6(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | (spl8_2 | ~spl8_8)),
% 0.21/0.51    inference(forward_demodulation,[],[f167,f120])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    k1_funct_1(sK1,sK0) = sK7(k2_relat_1(sK1)) | ~spl8_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    spl8_8 <=> k1_funct_1(sK1,sK0) = sK7(k2_relat_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    r2_hidden(sK7(k2_relat_1(sK1)),k2_relat_1(sK1)) | spl8_2),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f60,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ~spl8_2),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f163])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    $false | ~spl8_2),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f38,f154,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    r2_hidden(sK0,k1_xboole_0) | ~spl8_2),
% 0.21/0.51    inference(superposition,[],[f46,f140])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tarski(sK0) | ~spl8_2),
% 0.21/0.51    inference(backward_demodulation,[],[f21,f136])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(sK1) | ~spl8_2),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f19,f61,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(sK1) | ~spl8_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f59])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 0.21/0.51    inference(equality_resolution,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 0.21/0.51    inference(equality_resolution,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    spl8_2 | spl8_8 | ~spl8_4 | ~spl8_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f115,f93,f81,f118,f59])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    k1_funct_1(sK1,sK0) = sK7(k2_relat_1(sK1)) | k1_xboole_0 = k2_relat_1(sK1) | (~spl8_4 | ~spl8_6)),
% 0.21/0.51    inference(resolution,[],[f109,f37])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl8_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    $false | spl8_5),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f20,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ~v1_funct_1(sK1) | spl8_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    spl8_5 <=> v1_funct_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ~spl8_1 | ~spl8_5 | spl8_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f51,f93,f89,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    spl8_1 <=> v1_relat_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X1] : (r2_hidden(sK3(sK1,X1),k1_tarski(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X1,k2_relat_1(sK1))) )),
% 0.21/0.51    inference(superposition,[],[f43,f21])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X2,X0] : (r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.51    inference(equality_resolution,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl8_4 | ~spl8_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f55,f81])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X1] : (~v1_relat_1(sK1) | k1_funct_1(sK1,sK3(sK1,X1)) = X1 | ~r2_hidden(X1,k2_relat_1(sK1))) )),
% 0.21/0.51    inference(resolution,[],[f20,f42])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl8_1),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    $false | spl8_1),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f19,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | spl8_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f55])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (5178)------------------------------
% 0.21/0.51  % (5178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5178)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (5178)Memory used [KB]: 6268
% 0.21/0.51  % (5178)Time elapsed: 0.093 s
% 0.21/0.51  % (5178)------------------------------
% 0.21/0.51  % (5178)------------------------------
% 0.21/0.52  % (5162)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (5153)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (5175)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (5167)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (5152)Success in time 0.166 s
%------------------------------------------------------------------------------
