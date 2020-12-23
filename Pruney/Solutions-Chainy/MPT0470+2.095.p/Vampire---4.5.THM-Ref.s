%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 122 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  168 ( 358 expanded)
%              Number of equality atoms :   27 (  48 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f315,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f57,f64,f162,f314])).

fof(f314,plain,
    ( ~ spl7_1
    | spl7_2
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f312,f52])).

fof(f52,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl7_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f312,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f311,f87])).

fof(f87,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
    | ~ spl7_4 ),
    inference(resolution,[],[f72,f37])).

fof(f37,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f72,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k1_xboole_0) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f66,f18])).

fof(f18,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f66,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | r2_hidden(k4_tarski(X0,X1),X2)
        | ~ r1_tarski(k1_xboole_0,X2) )
    | ~ spl7_4 ),
    inference(resolution,[],[f63,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f63,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl7_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f311,plain,
    ( r2_hidden(k4_tarski(sK1(sK0,k1_xboole_0,k1_xboole_0),sK2(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(resolution,[],[f98,f63])).

fof(f98,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(X4)
        | r2_hidden(k4_tarski(sK1(sK0,k1_xboole_0,X4),sK2(sK0,k1_xboole_0,X4)),X4)
        | k5_relat_1(sK0,k1_xboole_0) = X4 )
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f97,f63])).

fof(f97,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(X4)
        | ~ v1_relat_1(k1_xboole_0)
        | r2_hidden(k4_tarski(sK1(sK0,k1_xboole_0,X4),sK2(sK0,k1_xboole_0,X4)),X4)
        | k5_relat_1(sK0,k1_xboole_0) = X4 )
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(resolution,[],[f89,f47])).

fof(f47,plain,
    ( ! [X6,X7] :
        ( sP3(sK2(sK0,X6,X7),sK1(sK0,X6,X7),X6,sK0)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6)
        | r2_hidden(k4_tarski(sK1(sK0,X6,X7),sK2(sK0,X6,X7)),X7)
        | k5_relat_1(sK0,X6) = X7 )
    | ~ spl7_1 ),
    inference(resolution,[],[f41,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | sP3(sK2(X0,X1,X2),sK1(X0,X1,X2),X1,X0)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f41,plain,
    ( v1_relat_1(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl7_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f89,plain,
    ( ! [X2,X0,X1] : ~ sP3(X0,X1,k1_xboole_0,X2)
    | ~ spl7_4 ),
    inference(resolution,[],[f87,f22])).

fof(f22,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X3,X4),X4),X1)
      | ~ sP3(X4,X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f162,plain,
    ( ~ spl7_1
    | spl7_3
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl7_1
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f160,f56])).

fof(f56,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl7_3
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f160,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f159,f87])).

fof(f159,plain,
    ( r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK2(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(resolution,[],[f111,f63])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,X0),sK2(k1_xboole_0,sK0,X0)),X0)
        | k5_relat_1(k1_xboole_0,sK0) = X0 )
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(resolution,[],[f110,f41])).

fof(f110,plain,
    ( ! [X6,X7] :
        ( ~ v1_relat_1(X6)
        | ~ v1_relat_1(X7)
        | r2_hidden(k4_tarski(sK1(k1_xboole_0,X6,X7),sK2(k1_xboole_0,X6,X7)),X7)
        | k5_relat_1(k1_xboole_0,X6) = X7 )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f70,f90])).

fof(f90,plain,
    ( ! [X4,X5,X3] : ~ sP3(X3,X4,X5,k1_xboole_0)
    | ~ spl7_4 ),
    inference(resolution,[],[f87,f21])).

% (16252)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f21,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0)
      | ~ sP3(X4,X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f70,plain,
    ( ! [X6,X7] :
        ( ~ v1_relat_1(X6)
        | ~ v1_relat_1(X7)
        | sP3(sK2(k1_xboole_0,X6,X7),sK1(k1_xboole_0,X6,X7),X6,k1_xboole_0)
        | r2_hidden(k4_tarski(sK1(k1_xboole_0,X6,X7),sK2(k1_xboole_0,X6,X7)),X7)
        | k5_relat_1(k1_xboole_0,X6) = X7 )
    | ~ spl7_4 ),
    inference(resolution,[],[f63,f25])).

fof(f64,plain,
    ( spl7_4
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f58,f39,f61])).

fof(f58,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_1 ),
    inference(resolution,[],[f46,f19])).

fof(f19,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f46,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(sK0))
        | v1_relat_1(X5) )
    | ~ spl7_1 ),
    inference(resolution,[],[f41,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f57,plain,
    ( ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f16,f54,f50])).

fof(f16,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f42,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:52:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (16269)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (16253)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (16260)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (16263)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (16253)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f42,f57,f64,f162,f314])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    ~spl7_1 | spl7_2 | ~spl7_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f313])).
% 0.21/0.49  fof(f313,plain,(
% 0.21/0.49    $false | (~spl7_1 | spl7_2 | ~spl7_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f312,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl7_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl7_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl7_1 | ~spl7_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f311,f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_xboole_0)) ) | ~spl7_4),
% 0.21/0.49    inference(resolution,[],[f72,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.49    inference(equality_resolution,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(k4_tarski(X0,X1),k1_xboole_0)) ) | ~spl7_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f66,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_xboole_0) | r2_hidden(k4_tarski(X0,X1),X2) | ~r1_tarski(k1_xboole_0,X2)) ) | ~spl7_4),
% 0.21/0.49    inference(resolution,[],[f63,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    v1_relat_1(k1_xboole_0) | ~spl7_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl7_4 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.49  fof(f311,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK1(sK0,k1_xboole_0,k1_xboole_0),sK2(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl7_1 | ~spl7_4)),
% 0.21/0.49    inference(resolution,[],[f98,f63])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X4] : (~v1_relat_1(X4) | r2_hidden(k4_tarski(sK1(sK0,k1_xboole_0,X4),sK2(sK0,k1_xboole_0,X4)),X4) | k5_relat_1(sK0,k1_xboole_0) = X4) ) | (~spl7_1 | ~spl7_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f97,f63])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X4] : (~v1_relat_1(X4) | ~v1_relat_1(k1_xboole_0) | r2_hidden(k4_tarski(sK1(sK0,k1_xboole_0,X4),sK2(sK0,k1_xboole_0,X4)),X4) | k5_relat_1(sK0,k1_xboole_0) = X4) ) | (~spl7_1 | ~spl7_4)),
% 0.21/0.49    inference(resolution,[],[f89,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X6,X7] : (sP3(sK2(sK0,X6,X7),sK1(sK0,X6,X7),X6,sK0) | ~v1_relat_1(X7) | ~v1_relat_1(X6) | r2_hidden(k4_tarski(sK1(sK0,X6,X7),sK2(sK0,X6,X7)),X7) | k5_relat_1(sK0,X6) = X7) ) | ~spl7_1),
% 0.21/0.49    inference(resolution,[],[f41,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | sP3(sK2(X0,X1,X2),sK1(X0,X1,X2),X1,X0) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    v1_relat_1(sK0) | ~spl7_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    spl7_1 <=> v1_relat_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~sP3(X0,X1,k1_xboole_0,X2)) ) | ~spl7_4),
% 0.21/0.49    inference(resolution,[],[f87,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X4,X0,X3,X1] : (r2_hidden(k4_tarski(sK4(X0,X1,X3,X4),X4),X1) | ~sP3(X4,X3,X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ~spl7_1 | spl7_3 | ~spl7_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    $false | (~spl7_1 | spl7_3 | ~spl7_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f160,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl7_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl7_3 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl7_1 | ~spl7_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f159,f87])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK2(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl7_1 | ~spl7_4)),
% 0.21/0.49    inference(resolution,[],[f111,f63])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,X0),sK2(k1_xboole_0,sK0,X0)),X0) | k5_relat_1(k1_xboole_0,sK0) = X0) ) | (~spl7_1 | ~spl7_4)),
% 0.21/0.49    inference(resolution,[],[f110,f41])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X6,X7] : (~v1_relat_1(X6) | ~v1_relat_1(X7) | r2_hidden(k4_tarski(sK1(k1_xboole_0,X6,X7),sK2(k1_xboole_0,X6,X7)),X7) | k5_relat_1(k1_xboole_0,X6) = X7) ) | ~spl7_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f70,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~sP3(X3,X4,X5,k1_xboole_0)) ) | ~spl7_4),
% 0.21/0.49    inference(resolution,[],[f87,f21])).
% 0.21/0.49  % (16252)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X4,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0) | ~sP3(X4,X3,X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X6,X7] : (~v1_relat_1(X6) | ~v1_relat_1(X7) | sP3(sK2(k1_xboole_0,X6,X7),sK1(k1_xboole_0,X6,X7),X6,k1_xboole_0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,X6,X7),sK2(k1_xboole_0,X6,X7)),X7) | k5_relat_1(k1_xboole_0,X6) = X7) ) | ~spl7_4),
% 0.21/0.49    inference(resolution,[],[f63,f25])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl7_4 | ~spl7_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f58,f39,f61])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    v1_relat_1(k1_xboole_0) | ~spl7_1),
% 0.21/0.49    inference(resolution,[],[f46,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(sK0)) | v1_relat_1(X5)) ) | ~spl7_1),
% 0.21/0.49    inference(resolution,[],[f41,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ~spl7_2 | ~spl7_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f16,f54,f50])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    spl7_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f17,f39])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (16253)------------------------------
% 0.21/0.50  % (16253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16253)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (16253)Memory used [KB]: 10874
% 0.21/0.50  % (16253)Time elapsed: 0.060 s
% 0.21/0.50  % (16253)------------------------------
% 0.21/0.50  % (16253)------------------------------
% 0.21/0.50  % (16255)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (16249)Success in time 0.146 s
%------------------------------------------------------------------------------
