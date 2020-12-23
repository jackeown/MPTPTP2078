%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:12 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   54 (  61 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  139 ( 154 expanded)
%              Number of equality atoms :   37 (  40 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f47,f51,f69,f72,f76])).

fof(f76,plain,
    ( spl3_1
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f42,f74])).

fof(f74,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl3_6 ),
    inference(resolution,[],[f73,f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f73,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))
    | ~ spl3_6 ),
    inference(resolution,[],[f68,f56])).

fof(f56,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f30,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f30,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f68,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1,k1_xboole_0),k1_xboole_0)
        | ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(X0,X1,k1_xboole_0),k1_xboole_0)
        | ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f42,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f72,plain,
    ( ~ spl3_2
    | spl3_5 ),
    inference(avatar_split_clause,[],[f70,f64,f45])).

fof(f45,plain,
    ( spl3_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f64,plain,
    ( spl3_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f70,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_5 ),
    inference(resolution,[],[f65,f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f65,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f69,plain,
    ( ~ spl3_5
    | spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f62,f49,f67,f64])).

fof(f49,plain,
    ( spl3_3
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1,k1_xboole_0),k1_xboole_0)
        | ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl3_3 ),
    inference(superposition,[],[f34,f50])).

fof(f50,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
            & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
        & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f51,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f27,f49])).

fof(f27,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f47,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f45])).

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f43,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f41])).

fof(f24,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).

fof(f14,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:12:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (796622848)
% 0.13/0.37  ipcrm: permission denied for id (799866882)
% 0.13/0.37  ipcrm: permission denied for id (799932420)
% 0.13/0.37  ipcrm: permission denied for id (799965189)
% 0.13/0.37  ipcrm: permission denied for id (799997958)
% 0.13/0.38  ipcrm: permission denied for id (800030727)
% 0.13/0.38  ipcrm: permission denied for id (800063496)
% 0.13/0.38  ipcrm: permission denied for id (796786697)
% 0.13/0.38  ipcrm: permission denied for id (796819467)
% 0.13/0.38  ipcrm: permission denied for id (796852236)
% 0.13/0.38  ipcrm: permission denied for id (796885005)
% 0.13/0.39  ipcrm: permission denied for id (796917775)
% 0.13/0.39  ipcrm: permission denied for id (796950544)
% 0.13/0.39  ipcrm: permission denied for id (797016081)
% 0.13/0.39  ipcrm: permission denied for id (797048850)
% 0.13/0.39  ipcrm: permission denied for id (797147157)
% 0.13/0.39  ipcrm: permission denied for id (800227350)
% 0.13/0.40  ipcrm: permission denied for id (797212695)
% 0.13/0.40  ipcrm: permission denied for id (800260120)
% 0.13/0.40  ipcrm: permission denied for id (797343770)
% 0.13/0.40  ipcrm: permission denied for id (800325659)
% 0.13/0.40  ipcrm: permission denied for id (800423966)
% 0.13/0.41  ipcrm: permission denied for id (800456735)
% 0.13/0.41  ipcrm: permission denied for id (797474848)
% 0.13/0.41  ipcrm: permission denied for id (800489505)
% 0.13/0.41  ipcrm: permission denied for id (800522274)
% 0.13/0.41  ipcrm: permission denied for id (800555043)
% 0.13/0.41  ipcrm: permission denied for id (800653350)
% 0.13/0.42  ipcrm: permission denied for id (800686119)
% 0.22/0.42  ipcrm: permission denied for id (797605931)
% 0.22/0.42  ipcrm: permission denied for id (800817196)
% 0.22/0.42  ipcrm: permission denied for id (800849965)
% 0.22/0.42  ipcrm: permission denied for id (797704238)
% 0.22/0.43  ipcrm: permission denied for id (797769776)
% 0.22/0.43  ipcrm: permission denied for id (800915505)
% 0.22/0.43  ipcrm: permission denied for id (797835314)
% 0.22/0.43  ipcrm: permission denied for id (800981044)
% 0.22/0.43  ipcrm: permission denied for id (797868085)
% 0.22/0.43  ipcrm: permission denied for id (801013814)
% 0.22/0.44  ipcrm: permission denied for id (801046583)
% 0.22/0.44  ipcrm: permission denied for id (797966392)
% 0.22/0.44  ipcrm: permission denied for id (797999162)
% 0.22/0.44  ipcrm: permission denied for id (798031932)
% 0.22/0.44  ipcrm: permission denied for id (801177662)
% 0.22/0.45  ipcrm: permission denied for id (798163009)
% 0.22/0.45  ipcrm: permission denied for id (801275970)
% 0.22/0.45  ipcrm: permission denied for id (798228547)
% 0.22/0.45  ipcrm: permission denied for id (801308740)
% 0.22/0.45  ipcrm: permission denied for id (798326854)
% 0.22/0.46  ipcrm: permission denied for id (801407048)
% 0.22/0.46  ipcrm: permission denied for id (798425161)
% 0.22/0.46  ipcrm: permission denied for id (798457930)
% 0.22/0.46  ipcrm: permission denied for id (798490699)
% 0.22/0.46  ipcrm: permission denied for id (798556237)
% 0.22/0.46  ipcrm: permission denied for id (798589006)
% 0.22/0.47  ipcrm: permission denied for id (801505360)
% 0.22/0.47  ipcrm: permission denied for id (798654545)
% 0.22/0.47  ipcrm: permission denied for id (801538130)
% 0.22/0.47  ipcrm: permission denied for id (801570899)
% 0.22/0.47  ipcrm: permission denied for id (798720084)
% 0.22/0.47  ipcrm: permission denied for id (801603669)
% 0.22/0.48  ipcrm: permission denied for id (801636438)
% 0.22/0.48  ipcrm: permission denied for id (798785623)
% 0.22/0.48  ipcrm: permission denied for id (798818392)
% 0.22/0.48  ipcrm: permission denied for id (798851161)
% 0.22/0.48  ipcrm: permission denied for id (801669210)
% 0.22/0.48  ipcrm: permission denied for id (798916699)
% 0.22/0.49  ipcrm: permission denied for id (801701980)
% 0.22/0.49  ipcrm: permission denied for id (798982238)
% 0.22/0.49  ipcrm: permission denied for id (801767519)
% 0.22/0.49  ipcrm: permission denied for id (799047776)
% 0.22/0.50  ipcrm: permission denied for id (799146083)
% 0.22/0.50  ipcrm: permission denied for id (799178852)
% 0.22/0.50  ipcrm: permission denied for id (799211621)
% 0.22/0.50  ipcrm: permission denied for id (801898599)
% 0.22/0.51  ipcrm: permission denied for id (799375465)
% 0.22/0.51  ipcrm: permission denied for id (799408234)
% 0.22/0.51  ipcrm: permission denied for id (799441004)
% 0.22/0.52  ipcrm: permission denied for id (802062447)
% 0.22/0.52  ipcrm: permission denied for id (802095216)
% 0.22/0.53  ipcrm: permission denied for id (799572086)
% 0.22/0.53  ipcrm: permission denied for id (799604855)
% 0.22/0.53  ipcrm: permission denied for id (799637624)
% 0.22/0.53  ipcrm: permission denied for id (799670393)
% 0.22/0.53  ipcrm: permission denied for id (799703163)
% 0.22/0.53  ipcrm: permission denied for id (802324604)
% 0.22/0.54  ipcrm: permission denied for id (799768701)
% 0.22/0.54  ipcrm: permission denied for id (802357374)
% 0.22/0.54  ipcrm: permission denied for id (799801471)
% 0.91/0.67  % (31407)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.24/0.68  % (31410)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.24/0.68  % (31408)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.24/0.68  % (31415)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.24/0.68  % (31408)Refutation found. Thanks to Tanya!
% 1.24/0.68  % SZS status Theorem for theBenchmark
% 1.24/0.68  % (31418)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.24/0.69  % (31416)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 1.24/0.69  % SZS output start Proof for theBenchmark
% 1.24/0.69  fof(f77,plain,(
% 1.24/0.69    $false),
% 1.24/0.69    inference(avatar_sat_refutation,[],[f43,f47,f51,f69,f72,f76])).
% 1.24/0.69  fof(f76,plain,(
% 1.24/0.69    spl3_1 | ~spl3_6),
% 1.24/0.69    inference(avatar_contradiction_clause,[],[f75])).
% 1.24/0.69  fof(f75,plain,(
% 1.24/0.69    $false | (spl3_1 | ~spl3_6)),
% 1.24/0.69    inference(subsumption_resolution,[],[f42,f74])).
% 1.24/0.69  fof(f74,plain,(
% 1.24/0.69    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | ~spl3_6),
% 1.24/0.69    inference(resolution,[],[f73,f29])).
% 1.24/0.69  fof(f29,plain,(
% 1.24/0.69    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 1.24/0.69    inference(cnf_transformation,[],[f17])).
% 1.24/0.69  fof(f17,plain,(
% 1.24/0.69    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 1.24/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f16])).
% 1.24/0.69  fof(f16,plain,(
% 1.24/0.69    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 1.24/0.69    introduced(choice_axiom,[])).
% 1.24/0.69  fof(f12,plain,(
% 1.24/0.69    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.24/0.69    inference(ennf_transformation,[],[f2])).
% 1.24/0.69  fof(f2,axiom,(
% 1.24/0.69    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.24/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.24/0.69  fof(f73,plain,(
% 1.24/0.69    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))) ) | ~spl3_6),
% 1.24/0.69    inference(resolution,[],[f68,f56])).
% 1.24/0.69  fof(f56,plain,(
% 1.24/0.69    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.24/0.69    inference(superposition,[],[f30,f38])).
% 1.24/0.69  fof(f38,plain,(
% 1.24/0.69    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.24/0.69    inference(equality_resolution,[],[f33])).
% 1.24/0.69  fof(f33,plain,(
% 1.24/0.69    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.24/0.69    inference(cnf_transformation,[],[f19])).
% 1.24/0.69  fof(f19,plain,(
% 1.24/0.69    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.24/0.69    inference(flattening,[],[f18])).
% 1.24/0.69  fof(f18,plain,(
% 1.24/0.69    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.24/0.69    inference(nnf_transformation,[],[f3])).
% 1.24/0.69  fof(f3,axiom,(
% 1.24/0.69    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.24/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.24/0.69  fof(f30,plain,(
% 1.24/0.69    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.24/0.69    inference(cnf_transformation,[],[f4])).
% 1.24/0.69  fof(f4,axiom,(
% 1.24/0.69    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.24/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.24/0.69  fof(f68,plain,(
% 1.24/0.69    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,k1_xboole_0),k1_xboole_0) | ~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))) ) | ~spl3_6),
% 1.24/0.69    inference(avatar_component_clause,[],[f67])).
% 1.24/0.69  fof(f67,plain,(
% 1.24/0.69    spl3_6 <=> ! [X1,X0] : (r2_hidden(sK2(X0,X1,k1_xboole_0),k1_xboole_0) | ~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)))),
% 1.24/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.24/0.69  fof(f42,plain,(
% 1.24/0.69    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl3_1),
% 1.24/0.69    inference(avatar_component_clause,[],[f41])).
% 1.24/0.69  fof(f41,plain,(
% 1.24/0.69    spl3_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 1.24/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.24/0.69  fof(f72,plain,(
% 1.24/0.69    ~spl3_2 | spl3_5),
% 1.24/0.69    inference(avatar_split_clause,[],[f70,f64,f45])).
% 1.24/0.69  fof(f45,plain,(
% 1.24/0.69    spl3_2 <=> v1_xboole_0(k1_xboole_0)),
% 1.24/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.24/0.69  fof(f64,plain,(
% 1.24/0.69    spl3_5 <=> v1_relat_1(k1_xboole_0)),
% 1.24/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.24/0.69  fof(f70,plain,(
% 1.24/0.69    ~v1_xboole_0(k1_xboole_0) | spl3_5),
% 1.24/0.69    inference(resolution,[],[f65,f28])).
% 1.24/0.69  fof(f28,plain,(
% 1.24/0.69    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.24/0.69    inference(cnf_transformation,[],[f11])).
% 1.24/0.69  fof(f11,plain,(
% 1.24/0.69    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.24/0.69    inference(ennf_transformation,[],[f5])).
% 1.24/0.69  fof(f5,axiom,(
% 1.24/0.69    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.24/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.24/0.69  fof(f65,plain,(
% 1.24/0.69    ~v1_relat_1(k1_xboole_0) | spl3_5),
% 1.24/0.69    inference(avatar_component_clause,[],[f64])).
% 1.24/0.69  fof(f69,plain,(
% 1.24/0.69    ~spl3_5 | spl3_6 | ~spl3_3),
% 1.24/0.69    inference(avatar_split_clause,[],[f62,f49,f67,f64])).
% 1.24/0.69  fof(f49,plain,(
% 1.24/0.69    spl3_3 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.24/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.24/0.69  fof(f62,plain,(
% 1.24/0.69    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,k1_xboole_0),k1_xboole_0) | ~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl3_3),
% 1.24/0.69    inference(superposition,[],[f34,f50])).
% 1.24/0.69  fof(f50,plain,(
% 1.24/0.69    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl3_3),
% 1.24/0.69    inference(avatar_component_clause,[],[f49])).
% 1.24/0.69  fof(f34,plain,(
% 1.24/0.69    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.24/0.69    inference(cnf_transformation,[],[f23])).
% 1.24/0.69  fof(f23,plain,(
% 1.24/0.69    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.24/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 1.24/0.69  fof(f22,plain,(
% 1.24/0.69    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))))),
% 1.24/0.69    introduced(choice_axiom,[])).
% 1.24/0.69  fof(f21,plain,(
% 1.24/0.69    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.24/0.69    inference(rectify,[],[f20])).
% 1.24/0.69  fof(f20,plain,(
% 1.24/0.69    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.24/0.69    inference(nnf_transformation,[],[f13])).
% 1.24/0.69  fof(f13,plain,(
% 1.24/0.69    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.24/0.69    inference(ennf_transformation,[],[f6])).
% 1.24/0.69  fof(f6,axiom,(
% 1.24/0.69    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.24/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 1.24/0.69  fof(f51,plain,(
% 1.24/0.69    spl3_3),
% 1.24/0.69    inference(avatar_split_clause,[],[f27,f49])).
% 1.24/0.69  fof(f27,plain,(
% 1.24/0.69    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.24/0.69    inference(cnf_transformation,[],[f7])).
% 1.24/0.69  fof(f7,axiom,(
% 1.24/0.69    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.24/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.24/0.69  fof(f47,plain,(
% 1.24/0.69    spl3_2),
% 1.24/0.69    inference(avatar_split_clause,[],[f25,f45])).
% 1.24/0.69  fof(f25,plain,(
% 1.24/0.69    v1_xboole_0(k1_xboole_0)),
% 1.24/0.69    inference(cnf_transformation,[],[f1])).
% 1.24/0.69  fof(f1,axiom,(
% 1.24/0.69    v1_xboole_0(k1_xboole_0)),
% 1.24/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.24/0.69  fof(f43,plain,(
% 1.24/0.69    ~spl3_1),
% 1.24/0.69    inference(avatar_split_clause,[],[f24,f41])).
% 1.24/0.69  fof(f24,plain,(
% 1.24/0.69    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.24/0.69    inference(cnf_transformation,[],[f15])).
% 1.24/0.69  fof(f15,plain,(
% 1.24/0.69    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.24/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).
% 1.24/0.69  fof(f14,plain,(
% 1.24/0.69    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.24/0.69    introduced(choice_axiom,[])).
% 1.24/0.69  fof(f10,plain,(
% 1.24/0.69    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 1.24/0.69    inference(ennf_transformation,[],[f9])).
% 1.24/0.69  fof(f9,negated_conjecture,(
% 1.24/0.69    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.24/0.69    inference(negated_conjecture,[],[f8])).
% 1.24/0.69  fof(f8,conjecture,(
% 1.24/0.69    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.24/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 1.24/0.69  % SZS output end Proof for theBenchmark
% 1.24/0.69  % (31408)------------------------------
% 1.24/0.69  % (31408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.69  % (31408)Termination reason: Refutation
% 1.24/0.69  
% 1.24/0.69  % (31408)Memory used [KB]: 10618
% 1.24/0.69  % (31408)Time elapsed: 0.076 s
% 1.24/0.69  % (31408)------------------------------
% 1.24/0.69  % (31408)------------------------------
% 1.24/0.69  % (31231)Success in time 0.327 s
%------------------------------------------------------------------------------
