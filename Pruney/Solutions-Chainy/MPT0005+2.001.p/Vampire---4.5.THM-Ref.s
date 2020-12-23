%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:30 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   41 (  61 expanded)
%              Number of leaves         :    7 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  118 ( 196 expanded)
%              Number of equality atoms :    2 (   3 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f34,f43,f61,f64,f68])).

fof(f68,plain,
    ( ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f66,f38])).

fof(f38,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl6_3
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f66,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(resolution,[],[f41,f29])).

fof(f29,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f27,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f27,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl6_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f41,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl6_4
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f64,plain,
    ( ~ spl6_3
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | ~ spl6_3
    | spl6_4 ),
    inference(subsumption_resolution,[],[f62,f38])).

fof(f62,plain,
    ( ~ r2_hidden(sK2,sK0)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f9,f42])).

fof(f42,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f9,plain,
    ( ~ r2_hidden(sK2,sK0)
    | r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1) )
      & ( r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) )
      & r2_hidden(X2,k2_xboole_0(X0,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
          & ~ ( ~ r2_hidden(X2,X1)
              & r2_hidden(X2,X0) )
          & r2_hidden(X2,k2_xboole_0(X0,X1))
          & r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).

fof(f61,plain,
    ( ~ spl6_2
    | spl6_3
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f60])).

fof(f60,plain,
    ( $false
    | ~ spl6_2
    | spl6_3
    | spl6_4 ),
    inference(subsumption_resolution,[],[f57,f42])).

fof(f57,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl6_2
    | spl6_3 ),
    inference(resolution,[],[f51,f33])).

fof(f33,plain,
    ( r2_hidden(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl6_2
  <=> r2_hidden(sK2,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f51,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK2,k2_xboole_0(sK0,X2))
        | r2_hidden(sK2,X2) )
    | spl6_3 ),
    inference(resolution,[],[f44,f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f44,plain,
    ( ! [X0] :
        ( ~ sP5(sK2,X0,sK0)
        | r2_hidden(sK2,X0) )
    | spl6_3 ),
    inference(resolution,[],[f37,f17])).

fof(f17,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f37,plain,
    ( ~ r2_hidden(sK2,sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f43,plain,
    ( spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f8,f40,f36])).

fof(f8,plain,
    ( ~ r2_hidden(sK2,sK1)
    | r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f34,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f11,f31])).

fof(f11,plain,(
    r2_hidden(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f28,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f10,f25])).

fof(f10,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:57:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (828669952)
% 0.14/0.37  ipcrm: permission denied for id (828702721)
% 0.14/0.37  ipcrm: permission denied for id (829227012)
% 0.14/0.37  ipcrm: permission denied for id (829259781)
% 0.14/0.38  ipcrm: permission denied for id (829358088)
% 0.14/0.38  ipcrm: permission denied for id (829390857)
% 0.14/0.38  ipcrm: permission denied for id (829423626)
% 0.14/0.38  ipcrm: permission denied for id (829521933)
% 0.14/0.39  ipcrm: permission denied for id (829620240)
% 0.14/0.39  ipcrm: permission denied for id (829653009)
% 0.14/0.39  ipcrm: permission denied for id (829718547)
% 0.14/0.39  ipcrm: permission denied for id (829784085)
% 0.14/0.39  ipcrm: permission denied for id (828801046)
% 0.22/0.40  ipcrm: permission denied for id (829816855)
% 0.22/0.40  ipcrm: permission denied for id (829849624)
% 0.22/0.40  ipcrm: permission denied for id (829882393)
% 0.22/0.40  ipcrm: permission denied for id (829915162)
% 0.22/0.40  ipcrm: permission denied for id (829980700)
% 0.22/0.40  ipcrm: permission denied for id (830013469)
% 0.22/0.40  ipcrm: permission denied for id (830046238)
% 0.22/0.41  ipcrm: permission denied for id (830275621)
% 0.22/0.41  ipcrm: permission denied for id (830308390)
% 0.22/0.41  ipcrm: permission denied for id (830341159)
% 0.22/0.42  ipcrm: permission denied for id (830373928)
% 0.22/0.42  ipcrm: permission denied for id (828899370)
% 0.22/0.42  ipcrm: permission denied for id (830570543)
% 0.22/0.43  ipcrm: permission denied for id (830636081)
% 0.22/0.43  ipcrm: permission denied for id (830701619)
% 0.22/0.43  ipcrm: permission denied for id (830832695)
% 0.22/0.44  ipcrm: permission denied for id (830898233)
% 0.22/0.44  ipcrm: permission denied for id (830931002)
% 0.22/0.44  ipcrm: permission denied for id (830963771)
% 0.22/0.45  ipcrm: permission denied for id (829030465)
% 0.22/0.45  ipcrm: permission denied for id (831160386)
% 0.22/0.45  ipcrm: permission denied for id (831193155)
% 0.22/0.45  ipcrm: permission denied for id (831225924)
% 0.22/0.45  ipcrm: permission denied for id (831291462)
% 0.22/0.46  ipcrm: permission denied for id (831389769)
% 0.22/0.46  ipcrm: permission denied for id (829063242)
% 0.22/0.46  ipcrm: permission denied for id (831455308)
% 0.22/0.46  ipcrm: permission denied for id (831488077)
% 0.22/0.47  ipcrm: permission denied for id (831586384)
% 0.22/0.47  ipcrm: permission denied for id (831651922)
% 0.22/0.47  ipcrm: permission denied for id (831717460)
% 0.22/0.47  ipcrm: permission denied for id (831750229)
% 0.22/0.48  ipcrm: permission denied for id (831848536)
% 0.22/0.48  ipcrm: permission denied for id (831881305)
% 0.22/0.48  ipcrm: permission denied for id (831946843)
% 0.22/0.48  ipcrm: permission denied for id (832012381)
% 0.22/0.48  ipcrm: permission denied for id (832045150)
% 0.22/0.48  ipcrm: permission denied for id (832077919)
% 0.22/0.49  ipcrm: permission denied for id (832110688)
% 0.22/0.49  ipcrm: permission denied for id (832143457)
% 0.22/0.49  ipcrm: permission denied for id (832307302)
% 0.22/0.49  ipcrm: permission denied for id (832340071)
% 0.22/0.50  ipcrm: permission denied for id (832405609)
% 0.22/0.50  ipcrm: permission denied for id (832438378)
% 0.22/0.50  ipcrm: permission denied for id (832471147)
% 0.22/0.50  ipcrm: permission denied for id (832503916)
% 0.22/0.50  ipcrm: permission denied for id (832569454)
% 0.22/0.51  ipcrm: permission denied for id (832634992)
% 0.22/0.51  ipcrm: permission denied for id (832733299)
% 0.22/0.51  ipcrm: permission denied for id (832766068)
% 0.35/0.51  ipcrm: permission denied for id (832798837)
% 0.35/0.52  ipcrm: permission denied for id (829128823)
% 0.35/0.52  ipcrm: permission denied for id (832929914)
% 0.35/0.52  ipcrm: permission denied for id (832962683)
% 0.35/0.52  ipcrm: permission denied for id (833093759)
% 0.39/0.59  % (30206)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.39/0.60  % (30214)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.39/0.60  % (30206)Refutation found. Thanks to Tanya!
% 0.39/0.60  % SZS status Theorem for theBenchmark
% 0.39/0.60  % SZS output start Proof for theBenchmark
% 0.39/0.60  fof(f69,plain,(
% 0.39/0.60    $false),
% 0.39/0.60    inference(avatar_sat_refutation,[],[f28,f34,f43,f61,f64,f68])).
% 0.39/0.60  fof(f68,plain,(
% 0.39/0.60    ~spl6_1 | ~spl6_3 | ~spl6_4),
% 0.39/0.60    inference(avatar_contradiction_clause,[],[f67])).
% 0.39/0.60  fof(f67,plain,(
% 0.39/0.60    $false | (~spl6_1 | ~spl6_3 | ~spl6_4)),
% 0.39/0.60    inference(subsumption_resolution,[],[f66,f38])).
% 0.39/0.60  fof(f38,plain,(
% 0.39/0.60    r2_hidden(sK2,sK0) | ~spl6_3),
% 0.39/0.60    inference(avatar_component_clause,[],[f36])).
% 0.39/0.60  fof(f36,plain,(
% 0.39/0.60    spl6_3 <=> r2_hidden(sK2,sK0)),
% 0.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.39/0.60  fof(f66,plain,(
% 0.39/0.60    ~r2_hidden(sK2,sK0) | (~spl6_1 | ~spl6_4)),
% 0.39/0.60    inference(resolution,[],[f41,f29])).
% 0.39/0.60  fof(f29,plain,(
% 0.39/0.60    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl6_1),
% 0.39/0.60    inference(resolution,[],[f27,f12])).
% 0.39/0.60  fof(f12,plain,(
% 0.39/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.39/0.60    inference(cnf_transformation,[],[f7])).
% 0.39/0.60  fof(f7,plain,(
% 0.39/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.39/0.60    inference(ennf_transformation,[],[f5])).
% 0.39/0.60  fof(f5,plain,(
% 0.39/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.39/0.60    inference(rectify,[],[f2])).
% 0.39/0.60  fof(f2,axiom,(
% 0.39/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.39/0.60  fof(f27,plain,(
% 0.39/0.60    r1_xboole_0(sK0,sK1) | ~spl6_1),
% 0.39/0.60    inference(avatar_component_clause,[],[f25])).
% 0.39/0.60  fof(f25,plain,(
% 0.39/0.60    spl6_1 <=> r1_xboole_0(sK0,sK1)),
% 0.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.39/0.60  fof(f41,plain,(
% 0.39/0.60    r2_hidden(sK2,sK1) | ~spl6_4),
% 0.39/0.60    inference(avatar_component_clause,[],[f40])).
% 0.39/0.60  fof(f40,plain,(
% 0.39/0.60    spl6_4 <=> r2_hidden(sK2,sK1)),
% 0.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.39/0.60  fof(f64,plain,(
% 0.39/0.60    ~spl6_3 | spl6_4),
% 0.39/0.60    inference(avatar_contradiction_clause,[],[f63])).
% 0.39/0.60  fof(f63,plain,(
% 0.39/0.60    $false | (~spl6_3 | spl6_4)),
% 0.39/0.60    inference(subsumption_resolution,[],[f62,f38])).
% 0.39/0.60  fof(f62,plain,(
% 0.39/0.60    ~r2_hidden(sK2,sK0) | spl6_4),
% 0.39/0.60    inference(subsumption_resolution,[],[f9,f42])).
% 0.39/0.60  fof(f42,plain,(
% 0.39/0.60    ~r2_hidden(sK2,sK1) | spl6_4),
% 0.39/0.60    inference(avatar_component_clause,[],[f40])).
% 0.39/0.60  fof(f9,plain,(
% 0.39/0.60    ~r2_hidden(sK2,sK0) | r2_hidden(sK2,sK1)),
% 0.39/0.60    inference(cnf_transformation,[],[f6])).
% 0.39/0.60  fof(f6,plain,(
% 0.39/0.60    ? [X0,X1,X2] : ((r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) & (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 0.39/0.60    inference(ennf_transformation,[],[f4])).
% 0.39/0.60  fof(f4,negated_conjecture,(
% 0.39/0.60    ~! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 0.39/0.60    inference(negated_conjecture,[],[f3])).
% 0.39/0.60  fof(f3,conjecture,(
% 0.39/0.60    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 0.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).
% 0.39/0.60  fof(f61,plain,(
% 0.39/0.60    ~spl6_2 | spl6_3 | spl6_4),
% 0.39/0.60    inference(avatar_contradiction_clause,[],[f60])).
% 0.39/0.60  fof(f60,plain,(
% 0.39/0.60    $false | (~spl6_2 | spl6_3 | spl6_4)),
% 0.39/0.60    inference(subsumption_resolution,[],[f57,f42])).
% 0.39/0.60  fof(f57,plain,(
% 0.39/0.60    r2_hidden(sK2,sK1) | (~spl6_2 | spl6_3)),
% 0.39/0.60    inference(resolution,[],[f51,f33])).
% 0.39/0.60  fof(f33,plain,(
% 0.39/0.60    r2_hidden(sK2,k2_xboole_0(sK0,sK1)) | ~spl6_2),
% 0.39/0.60    inference(avatar_component_clause,[],[f31])).
% 0.39/0.60  fof(f31,plain,(
% 0.39/0.60    spl6_2 <=> r2_hidden(sK2,k2_xboole_0(sK0,sK1))),
% 0.39/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.39/0.60  fof(f51,plain,(
% 0.39/0.60    ( ! [X2] : (~r2_hidden(sK2,k2_xboole_0(sK0,X2)) | r2_hidden(sK2,X2)) ) | spl6_3),
% 0.39/0.60    inference(resolution,[],[f44,f22])).
% 0.39/0.60  fof(f22,plain,(
% 0.39/0.60    ( ! [X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.39/0.60    inference(equality_resolution,[],[f19])).
% 0.39/0.60  fof(f19,plain,(
% 0.39/0.60    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.39/0.60    inference(cnf_transformation,[],[f1])).
% 0.39/0.60  fof(f1,axiom,(
% 0.39/0.60    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.39/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.39/0.60  fof(f44,plain,(
% 0.39/0.60    ( ! [X0] : (~sP5(sK2,X0,sK0) | r2_hidden(sK2,X0)) ) | spl6_3),
% 0.39/0.60    inference(resolution,[],[f37,f17])).
% 0.39/0.60  fof(f17,plain,(
% 0.39/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~sP5(X3,X1,X0)) )),
% 0.39/0.60    inference(cnf_transformation,[],[f1])).
% 0.39/0.60  fof(f37,plain,(
% 0.39/0.60    ~r2_hidden(sK2,sK0) | spl6_3),
% 0.39/0.60    inference(avatar_component_clause,[],[f36])).
% 0.39/0.60  fof(f43,plain,(
% 0.39/0.60    spl6_3 | ~spl6_4),
% 0.39/0.60    inference(avatar_split_clause,[],[f8,f40,f36])).
% 0.39/0.60  fof(f8,plain,(
% 0.39/0.60    ~r2_hidden(sK2,sK1) | r2_hidden(sK2,sK0)),
% 0.39/0.60    inference(cnf_transformation,[],[f6])).
% 0.39/0.60  fof(f34,plain,(
% 0.39/0.60    spl6_2),
% 0.39/0.60    inference(avatar_split_clause,[],[f11,f31])).
% 0.39/0.60  fof(f11,plain,(
% 0.39/0.60    r2_hidden(sK2,k2_xboole_0(sK0,sK1))),
% 0.39/0.60    inference(cnf_transformation,[],[f6])).
% 0.39/0.60  fof(f28,plain,(
% 0.39/0.60    spl6_1),
% 0.39/0.60    inference(avatar_split_clause,[],[f10,f25])).
% 0.39/0.60  fof(f10,plain,(
% 0.39/0.60    r1_xboole_0(sK0,sK1)),
% 0.39/0.60    inference(cnf_transformation,[],[f6])).
% 0.39/0.60  % SZS output end Proof for theBenchmark
% 0.39/0.60  % (30206)------------------------------
% 0.39/0.60  % (30206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.60  % (30206)Termination reason: Refutation
% 0.39/0.60  
% 0.39/0.60  % (30206)Memory used [KB]: 10618
% 0.39/0.60  % (30206)Time elapsed: 0.035 s
% 0.39/0.60  % (30206)------------------------------
% 0.39/0.60  % (30206)------------------------------
% 0.39/0.60  % (30027)Success in time 0.24 s
%------------------------------------------------------------------------------
