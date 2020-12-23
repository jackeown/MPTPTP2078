%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:58 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :   57 (  73 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  142 ( 186 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f54,f56,f65,f68,f71])).

fof(f71,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f64,f19])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

fof(f64,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f68,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f61,f20])).

fof(f20,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,
    ( ~ v1_funct_1(sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f65,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f58,f46,f63,f60])).

fof(f46,plain,
    ( spl3_3
  <=> ! [X0] :
        ( r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0)
        | v5_funct_1(k1_xboole_0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f58,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f57,f21])).

fof(f21,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,
    ( ! [X0] :
        ( v5_funct_1(k1_xboole_0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f47,f35])).

fof(f35,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(global_subsumption,[],[f25,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f32,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f25,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f47,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0)
        | v5_funct_1(k1_xboole_0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f56,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f55])).

fof(f55,plain,
    ( $false
    | spl3_2 ),
    inference(resolution,[],[f50,f22])).

fof(f22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f50,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_2 ),
    inference(resolution,[],[f44,f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f44,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_2
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f54,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f49,f22])).

fof(f49,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_1 ),
    inference(resolution,[],[f41,f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f41,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_1
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f48,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f38,f46,f43,f40])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | v5_funct_1(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f30,f23])).

fof(f23,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | v5_funct_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (822640641)
% 0.13/0.37  ipcrm: permission denied for id (825229314)
% 0.13/0.38  ipcrm: permission denied for id (822870027)
% 0.13/0.38  ipcrm: permission denied for id (825524236)
% 0.13/0.38  ipcrm: permission denied for id (822902798)
% 0.13/0.38  ipcrm: permission denied for id (822968336)
% 0.13/0.38  ipcrm: permission denied for id (823001105)
% 0.13/0.39  ipcrm: permission denied for id (825622546)
% 0.13/0.39  ipcrm: permission denied for id (825655315)
% 0.13/0.39  ipcrm: permission denied for id (823066644)
% 0.13/0.39  ipcrm: permission denied for id (825720854)
% 0.13/0.39  ipcrm: permission denied for id (823164952)
% 0.13/0.40  ipcrm: permission denied for id (823197722)
% 0.13/0.40  ipcrm: permission denied for id (825819163)
% 0.13/0.40  ipcrm: permission denied for id (825851932)
% 0.13/0.40  ipcrm: permission denied for id (823230493)
% 0.13/0.40  ipcrm: permission denied for id (825884702)
% 0.13/0.40  ipcrm: permission denied for id (823263263)
% 0.13/0.40  ipcrm: permission denied for id (825917472)
% 0.13/0.40  ipcrm: permission denied for id (823328801)
% 0.13/0.41  ipcrm: permission denied for id (825950242)
% 0.13/0.41  ipcrm: permission denied for id (825983011)
% 0.13/0.41  ipcrm: permission denied for id (823394342)
% 0.13/0.41  ipcrm: permission denied for id (826081319)
% 0.13/0.41  ipcrm: permission denied for id (826114088)
% 0.13/0.42  ipcrm: permission denied for id (826245163)
% 0.13/0.42  ipcrm: permission denied for id (826343469)
% 0.13/0.42  ipcrm: permission denied for id (826441776)
% 0.21/0.42  ipcrm: permission denied for id (823459889)
% 0.21/0.43  ipcrm: permission denied for id (823492658)
% 0.21/0.43  ipcrm: permission denied for id (826507315)
% 0.21/0.43  ipcrm: permission denied for id (826572853)
% 0.21/0.43  ipcrm: permission denied for id (826671160)
% 0.21/0.43  ipcrm: permission denied for id (823689273)
% 0.21/0.44  ipcrm: permission denied for id (826703930)
% 0.21/0.44  ipcrm: permission denied for id (826736699)
% 0.21/0.44  ipcrm: permission denied for id (823754812)
% 0.21/0.44  ipcrm: permission denied for id (823787582)
% 0.21/0.44  ipcrm: permission denied for id (826835008)
% 0.21/0.44  ipcrm: permission denied for id (826900546)
% 0.21/0.45  ipcrm: permission denied for id (823885891)
% 0.21/0.45  ipcrm: permission denied for id (826933316)
% 0.21/0.45  ipcrm: permission denied for id (823951429)
% 0.21/0.45  ipcrm: permission denied for id (823984198)
% 0.21/0.45  ipcrm: permission denied for id (826966087)
% 0.21/0.45  ipcrm: permission denied for id (824049737)
% 0.21/0.45  ipcrm: permission denied for id (824082506)
% 0.21/0.46  ipcrm: permission denied for id (827031627)
% 0.21/0.46  ipcrm: permission denied for id (824115276)
% 0.21/0.46  ipcrm: permission denied for id (827064397)
% 0.21/0.46  ipcrm: permission denied for id (824180814)
% 0.21/0.46  ipcrm: permission denied for id (824213583)
% 0.21/0.46  ipcrm: permission denied for id (827097168)
% 0.21/0.46  ipcrm: permission denied for id (824246353)
% 0.21/0.46  ipcrm: permission denied for id (824279122)
% 0.21/0.47  ipcrm: permission denied for id (824311891)
% 0.21/0.47  ipcrm: permission denied for id (827129940)
% 0.21/0.47  ipcrm: permission denied for id (824377429)
% 0.21/0.47  ipcrm: permission denied for id (824410198)
% 0.21/0.47  ipcrm: permission denied for id (827162711)
% 0.21/0.47  ipcrm: permission denied for id (827228249)
% 0.21/0.47  ipcrm: permission denied for id (827261018)
% 0.21/0.48  ipcrm: permission denied for id (824442971)
% 0.21/0.48  ipcrm: permission denied for id (824475740)
% 0.21/0.48  ipcrm: permission denied for id (824541278)
% 0.21/0.48  ipcrm: permission denied for id (827326559)
% 0.21/0.48  ipcrm: permission denied for id (827359328)
% 0.21/0.48  ipcrm: permission denied for id (824606818)
% 0.21/0.49  ipcrm: permission denied for id (827424867)
% 0.21/0.49  ipcrm: permission denied for id (824705127)
% 0.21/0.49  ipcrm: permission denied for id (827588713)
% 0.21/0.49  ipcrm: permission denied for id (827621482)
% 0.21/0.49  ipcrm: permission denied for id (827654251)
% 0.21/0.49  ipcrm: permission denied for id (827687020)
% 0.21/0.50  ipcrm: permission denied for id (824868974)
% 0.21/0.50  ipcrm: permission denied for id (824901743)
% 0.21/0.50  ipcrm: permission denied for id (827752560)
% 0.21/0.50  ipcrm: permission denied for id (827785329)
% 0.21/0.50  ipcrm: permission denied for id (827850867)
% 0.21/0.50  ipcrm: permission denied for id (827916405)
% 0.21/0.51  ipcrm: permission denied for id (824967286)
% 0.21/0.51  ipcrm: permission denied for id (825032824)
% 0.21/0.51  ipcrm: permission denied for id (827981945)
% 0.21/0.51  ipcrm: permission denied for id (828014714)
% 0.21/0.51  ipcrm: permission denied for id (828047483)
% 0.21/0.51  ipcrm: permission denied for id (828080252)
% 0.21/0.51  ipcrm: permission denied for id (825098365)
% 0.21/0.52  ipcrm: permission denied for id (828145790)
% 0.21/0.52  ipcrm: permission denied for id (828178559)
% 0.21/0.61  % (28311)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.89/0.63  % (28317)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.03/0.63  % (28317)Refutation not found, incomplete strategy% (28317)------------------------------
% 1.03/0.63  % (28317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.03/0.64  % (28331)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.03/0.64  % (28317)Termination reason: Refutation not found, incomplete strategy
% 1.03/0.64  
% 1.03/0.64  % (28317)Memory used [KB]: 10490
% 1.03/0.64  % (28317)Time elapsed: 0.082 s
% 1.03/0.64  % (28317)------------------------------
% 1.03/0.64  % (28317)------------------------------
% 1.03/0.64  % (28330)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.03/0.64  % (28331)Refutation not found, incomplete strategy% (28331)------------------------------
% 1.03/0.64  % (28331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.03/0.64  % (28331)Termination reason: Refutation not found, incomplete strategy
% 1.03/0.64  
% 1.03/0.64  % (28331)Memory used [KB]: 1663
% 1.03/0.64  % (28331)Time elapsed: 0.086 s
% 1.03/0.64  % (28331)------------------------------
% 1.03/0.64  % (28331)------------------------------
% 1.03/0.65  % (28320)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.03/0.65  % (28330)Refutation not found, incomplete strategy% (28330)------------------------------
% 1.03/0.65  % (28330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.03/0.65  % (28330)Termination reason: Refutation not found, incomplete strategy
% 1.03/0.65  
% 1.03/0.65  % (28330)Memory used [KB]: 6140
% 1.03/0.65  % (28330)Time elapsed: 0.074 s
% 1.03/0.65  % (28330)------------------------------
% 1.03/0.65  % (28330)------------------------------
% 1.03/0.65  % (28320)Refutation not found, incomplete strategy% (28320)------------------------------
% 1.03/0.65  % (28320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.03/0.65  % (28320)Termination reason: Refutation not found, incomplete strategy
% 1.03/0.65  
% 1.03/0.65  % (28320)Memory used [KB]: 1663
% 1.03/0.65  % (28320)Time elapsed: 0.072 s
% 1.03/0.65  % (28320)------------------------------
% 1.03/0.65  % (28320)------------------------------
% 1.03/0.65  % (28325)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.03/0.66  % (28321)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.03/0.66  % (28310)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.03/0.66  % (28333)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.03/0.66  % (28321)Refutation found. Thanks to Tanya!
% 1.03/0.66  % SZS status Theorem for theBenchmark
% 1.03/0.66  % SZS output start Proof for theBenchmark
% 1.03/0.66  fof(f72,plain,(
% 1.03/0.66    $false),
% 1.03/0.66    inference(avatar_sat_refutation,[],[f48,f54,f56,f65,f68,f71])).
% 1.03/0.66  fof(f71,plain,(
% 1.03/0.66    spl3_5),
% 1.03/0.66    inference(avatar_contradiction_clause,[],[f69])).
% 1.03/0.66  fof(f69,plain,(
% 1.03/0.66    $false | spl3_5),
% 1.03/0.66    inference(resolution,[],[f64,f19])).
% 1.03/0.66  fof(f19,plain,(
% 1.03/0.66    v1_relat_1(sK0)),
% 1.03/0.66    inference(cnf_transformation,[],[f13])).
% 1.03/0.66  fof(f13,plain,(
% 1.03/0.66    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.03/0.66    inference(flattening,[],[f12])).
% 1.03/0.66  fof(f12,plain,(
% 1.03/0.66    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.03/0.66    inference(ennf_transformation,[],[f10])).
% 1.03/0.66  fof(f10,negated_conjecture,(
% 1.03/0.66    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 1.03/0.66    inference(negated_conjecture,[],[f9])).
% 1.03/0.66  fof(f9,conjecture,(
% 1.03/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 1.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).
% 1.03/0.66  fof(f64,plain,(
% 1.03/0.66    ~v1_relat_1(sK0) | spl3_5),
% 1.03/0.66    inference(avatar_component_clause,[],[f63])).
% 1.03/0.66  fof(f63,plain,(
% 1.03/0.66    spl3_5 <=> v1_relat_1(sK0)),
% 1.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.03/0.66  fof(f68,plain,(
% 1.03/0.66    spl3_4),
% 1.03/0.66    inference(avatar_contradiction_clause,[],[f66])).
% 1.03/0.66  fof(f66,plain,(
% 1.03/0.66    $false | spl3_4),
% 1.03/0.66    inference(resolution,[],[f61,f20])).
% 1.03/0.66  fof(f20,plain,(
% 1.03/0.66    v1_funct_1(sK0)),
% 1.03/0.66    inference(cnf_transformation,[],[f13])).
% 1.03/0.66  fof(f61,plain,(
% 1.03/0.66    ~v1_funct_1(sK0) | spl3_4),
% 1.03/0.66    inference(avatar_component_clause,[],[f60])).
% 1.03/0.66  fof(f60,plain,(
% 1.03/0.66    spl3_4 <=> v1_funct_1(sK0)),
% 1.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.03/0.66  fof(f65,plain,(
% 1.03/0.66    ~spl3_4 | ~spl3_5 | ~spl3_3),
% 1.03/0.66    inference(avatar_split_clause,[],[f58,f46,f63,f60])).
% 1.03/0.66  fof(f46,plain,(
% 1.03/0.66    spl3_3 <=> ! [X0] : (r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0) | v5_funct_1(k1_xboole_0,X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0))),
% 1.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.03/0.66  fof(f58,plain,(
% 1.03/0.66    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~spl3_3),
% 1.03/0.66    inference(resolution,[],[f57,f21])).
% 1.03/0.66  fof(f21,plain,(
% 1.03/0.66    ~v5_funct_1(k1_xboole_0,sK0)),
% 1.03/0.66    inference(cnf_transformation,[],[f13])).
% 1.03/0.66  fof(f57,plain,(
% 1.03/0.66    ( ! [X0] : (v5_funct_1(k1_xboole_0,X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0)) ) | ~spl3_3),
% 1.03/0.66    inference(resolution,[],[f47,f35])).
% 1.03/0.66  fof(f35,plain,(
% 1.03/0.66    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.03/0.66    inference(global_subsumption,[],[f25,f34])).
% 1.03/0.66  fof(f34,plain,(
% 1.03/0.66    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 1.03/0.66    inference(superposition,[],[f32,f26])).
% 1.03/0.66  fof(f26,plain,(
% 1.03/0.66    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.03/0.66    inference(cnf_transformation,[],[f3])).
% 1.03/0.66  fof(f3,axiom,(
% 1.03/0.66    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.03/0.66  fof(f32,plain,(
% 1.03/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.03/0.66    inference(cnf_transformation,[],[f18])).
% 1.03/0.66  fof(f18,plain,(
% 1.03/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.03/0.66    inference(ennf_transformation,[],[f11])).
% 1.03/0.66  fof(f11,plain,(
% 1.03/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.03/0.66    inference(rectify,[],[f2])).
% 1.03/0.66  fof(f2,axiom,(
% 1.03/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.03/0.66  fof(f25,plain,(
% 1.03/0.66    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.03/0.66    inference(cnf_transformation,[],[f4])).
% 1.03/0.66  fof(f4,axiom,(
% 1.03/0.66    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.03/0.66  fof(f47,plain,(
% 1.03/0.66    ( ! [X0] : (r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0) | v5_funct_1(k1_xboole_0,X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0)) ) | ~spl3_3),
% 1.03/0.66    inference(avatar_component_clause,[],[f46])).
% 1.03/0.66  fof(f56,plain,(
% 1.03/0.66    spl3_2),
% 1.03/0.66    inference(avatar_contradiction_clause,[],[f55])).
% 1.03/0.66  fof(f55,plain,(
% 1.03/0.66    $false | spl3_2),
% 1.03/0.66    inference(resolution,[],[f50,f22])).
% 1.03/0.66  fof(f22,plain,(
% 1.03/0.66    v1_xboole_0(k1_xboole_0)),
% 1.03/0.66    inference(cnf_transformation,[],[f1])).
% 1.03/0.66  fof(f1,axiom,(
% 1.03/0.66    v1_xboole_0(k1_xboole_0)),
% 1.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.03/0.66  fof(f50,plain,(
% 1.03/0.66    ~v1_xboole_0(k1_xboole_0) | spl3_2),
% 1.03/0.66    inference(resolution,[],[f44,f27])).
% 1.03/0.66  fof(f27,plain,(
% 1.03/0.66    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.03/0.66    inference(cnf_transformation,[],[f14])).
% 1.03/0.66  fof(f14,plain,(
% 1.03/0.66    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.03/0.66    inference(ennf_transformation,[],[f5])).
% 1.03/0.66  fof(f5,axiom,(
% 1.03/0.66    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.03/0.66  fof(f44,plain,(
% 1.03/0.66    ~v1_relat_1(k1_xboole_0) | spl3_2),
% 1.03/0.66    inference(avatar_component_clause,[],[f43])).
% 1.03/0.66  fof(f43,plain,(
% 1.03/0.66    spl3_2 <=> v1_relat_1(k1_xboole_0)),
% 1.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.03/0.66  fof(f54,plain,(
% 1.03/0.66    spl3_1),
% 1.03/0.66    inference(avatar_contradiction_clause,[],[f53])).
% 1.03/0.66  fof(f53,plain,(
% 1.03/0.66    $false | spl3_1),
% 1.03/0.66    inference(resolution,[],[f49,f22])).
% 1.03/0.66  fof(f49,plain,(
% 1.03/0.66    ~v1_xboole_0(k1_xboole_0) | spl3_1),
% 1.03/0.66    inference(resolution,[],[f41,f28])).
% 1.03/0.66  fof(f28,plain,(
% 1.03/0.66    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 1.03/0.66    inference(cnf_transformation,[],[f15])).
% 1.03/0.66  fof(f15,plain,(
% 1.03/0.66    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 1.03/0.66    inference(ennf_transformation,[],[f7])).
% 1.03/0.66  fof(f7,axiom,(
% 1.03/0.66    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 1.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).
% 1.03/0.66  fof(f41,plain,(
% 1.03/0.66    ~v1_funct_1(k1_xboole_0) | spl3_1),
% 1.03/0.66    inference(avatar_component_clause,[],[f40])).
% 1.03/0.66  fof(f40,plain,(
% 1.03/0.66    spl3_1 <=> v1_funct_1(k1_xboole_0)),
% 1.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.03/0.66  fof(f48,plain,(
% 1.03/0.66    ~spl3_1 | ~spl3_2 | spl3_3),
% 1.03/0.66    inference(avatar_split_clause,[],[f38,f46,f43,f40])).
% 1.03/0.66  fof(f38,plain,(
% 1.03/0.66    ( ! [X0] : (r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X0) | v5_funct_1(k1_xboole_0,X0)) )),
% 1.03/0.66    inference(superposition,[],[f30,f23])).
% 1.03/0.66  fof(f23,plain,(
% 1.03/0.66    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.03/0.66    inference(cnf_transformation,[],[f6])).
% 1.03/0.66  fof(f6,axiom,(
% 1.03/0.66    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.03/0.66  fof(f30,plain,(
% 1.03/0.66    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | v5_funct_1(X1,X0)) )),
% 1.03/0.66    inference(cnf_transformation,[],[f17])).
% 1.03/0.66  fof(f17,plain,(
% 1.03/0.66    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.03/0.66    inference(flattening,[],[f16])).
% 1.03/0.66  fof(f16,plain,(
% 1.03/0.66    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.03/0.66    inference(ennf_transformation,[],[f8])).
% 1.03/0.66  fof(f8,axiom,(
% 1.03/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 1.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
% 1.03/0.66  % SZS output end Proof for theBenchmark
% 1.03/0.66  % (28321)------------------------------
% 1.03/0.66  % (28321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.03/0.66  % (28321)Termination reason: Refutation
% 1.03/0.66  
% 1.03/0.66  % (28321)Memory used [KB]: 10618
% 1.03/0.66  % (28321)Time elapsed: 0.094 s
% 1.03/0.66  % (28321)------------------------------
% 1.03/0.66  % (28321)------------------------------
% 1.03/0.66  % (28333)Refutation not found, incomplete strategy% (28333)------------------------------
% 1.03/0.66  % (28333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.03/0.66  % (28333)Termination reason: Refutation not found, incomplete strategy
% 1.03/0.66  
% 1.03/0.66  % (28333)Memory used [KB]: 10618
% 1.03/0.66  % (28333)Time elapsed: 0.091 s
% 1.03/0.66  % (28333)------------------------------
% 1.03/0.66  % (28333)------------------------------
% 1.03/0.67  % (28168)Success in time 0.308 s
%------------------------------------------------------------------------------
