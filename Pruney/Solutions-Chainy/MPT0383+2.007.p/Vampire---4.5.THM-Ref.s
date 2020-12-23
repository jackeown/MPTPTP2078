%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 255 expanded)
%              Number of leaves         :   14 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  208 ( 869 expanded)
%              Number of equality atoms :   15 ( 107 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1400,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f236,f720,f1128,f1384,f1399])).

fof(f1399,plain,
    ( spl7_7
    | spl7_10
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f1398])).

fof(f1398,plain,
    ( $false
    | spl7_7
    | spl7_10
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f1397,f161])).

fof(f161,plain,
    ( ~ v1_xboole_0(sK1)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl7_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f1397,plain,
    ( v1_xboole_0(sK1)
    | spl7_10
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f1390,f235])).

fof(f235,plain,
    ( ~ m1_subset_1(sK5(sK3),sK1)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl7_10
  <=> m1_subset_1(sK5(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f1390,plain,
    ( m1_subset_1(sK5(sK3),sK1)
    | v1_xboole_0(sK1)
    | ~ spl7_22 ),
    inference(resolution,[],[f728,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f728,plain,
    ( r2_hidden(sK5(sK3),sK1)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f727])).

fof(f727,plain,
    ( spl7_22
  <=> r2_hidden(sK5(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f1384,plain,(
    spl7_22 ),
    inference(avatar_contradiction_clause,[],[f1379])).

fof(f1379,plain,
    ( $false
    | spl7_22 ),
    inference(resolution,[],[f1374,f100])).

fof(f100,plain,(
    r2_hidden(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f96,f27])).

fof(f27,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ! [X4] :
        ( ! [X5] :
            ( k4_tarski(X4,X5) != sK3
            | ~ m1_subset_1(X5,sK1) )
        | ~ m1_subset_1(X4,sK0) )
    & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    & r2_hidden(sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( ! [X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ m1_subset_1(X5,X1) )
            | ~ m1_subset_1(X4,X0) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) )
   => ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != sK3
              | ~ m1_subset_1(X5,sK1) )
          | ~ m1_subset_1(X4,sK0) )
      & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
      & r2_hidden(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != X3
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,X0) )
      & r1_tarski(X2,k2_zfmisc_1(X0,X1))
      & r2_hidden(X3,X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4] :
              ( m1_subset_1(X4,X0)
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => k4_tarski(X4,X5) != X3 ) )
          & r1_tarski(X2,k2_zfmisc_1(X0,X1))
          & r2_hidden(X3,X2) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4] :
            ( m1_subset_1(X4,X0)
           => ! [X5] :
                ( m1_subset_1(X5,X1)
               => k4_tarski(X4,X5) != X3 ) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_subset_1)).

fof(f96,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | r2_hidden(sK3,X0) ) ),
    inference(resolution,[],[f65,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f65,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(sK3),X0)
      | ~ r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f43,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f43,plain,(
    r1_tarski(k1_tarski(sK3),sK2) ),
    inference(resolution,[],[f26,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f26,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f1374,plain,
    ( ! [X3] : ~ r2_hidden(sK3,k2_zfmisc_1(X3,sK1))
    | spl7_22 ),
    inference(superposition,[],[f755,f120])).

fof(f120,plain,(
    sK3 = k4_tarski(sK4(sK3),sK5(sK3)) ),
    inference(resolution,[],[f100,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK4(X0),sK5(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK4(X0),sK5(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f10,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK4(X0),sK5(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f755,plain,
    ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,sK5(sK3)),k2_zfmisc_1(X3,sK1))
    | spl7_22 ),
    inference(resolution,[],[f729,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f729,plain,
    ( ~ r2_hidden(sK5(sK3),sK1)
    | spl7_22 ),
    inference(avatar_component_clause,[],[f727])).

fof(f1128,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f1120])).

fof(f1120,plain,
    ( $false
    | ~ spl7_7 ),
    inference(resolution,[],[f1107,f100])).

fof(f1107,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,sK1))
    | ~ spl7_7 ),
    inference(condensation,[],[f1105])).

fof(f1105,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,sK1))
        | ~ r2_hidden(X0,k2_zfmisc_1(X2,X3)) )
    | ~ spl7_7 ),
    inference(superposition,[],[f902,f29])).

fof(f902,plain,
    ( ! [X6,X7,X5] : ~ r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,sK1))
    | ~ spl7_7 ),
    inference(resolution,[],[f895,f31])).

fof(f895,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl7_7 ),
    inference(resolution,[],[f160,f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f160,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f159])).

fof(f720,plain,(
    spl7_9 ),
    inference(avatar_contradiction_clause,[],[f715])).

fof(f715,plain,
    ( $false
    | spl7_9 ),
    inference(resolution,[],[f709,f100])).

fof(f709,plain,
    ( ! [X0] : ~ r2_hidden(sK3,k2_zfmisc_1(sK0,X0))
    | spl7_9 ),
    inference(superposition,[],[f257,f120])).

fof(f257,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(sK4(sK3),X0),k2_zfmisc_1(sK0,X1))
    | spl7_9 ),
    inference(resolution,[],[f241,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f241,plain,
    ( ~ r2_hidden(sK4(sK3),sK0)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f239,f40])).

fof(f239,plain,
    ( ~ r2_hidden(sK4(sK3),sK0)
    | v1_xboole_0(sK0)
    | spl7_9 ),
    inference(resolution,[],[f231,f34])).

fof(f231,plain,
    ( ~ m1_subset_1(sK4(sK3),sK0)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl7_9
  <=> m1_subset_1(sK4(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f236,plain,
    ( ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f227,f233,f229])).

fof(f227,plain,
    ( ~ m1_subset_1(sK5(sK3),sK1)
    | ~ m1_subset_1(sK4(sK3),sK0) ),
    inference(trivial_inequality_removal,[],[f223])).

fof(f223,plain,
    ( sK3 != sK3
    | ~ m1_subset_1(sK5(sK3),sK1)
    | ~ m1_subset_1(sK4(sK3),sK0) ),
    inference(superposition,[],[f28,f120])).

fof(f28,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK3
      | ~ m1_subset_1(X5,sK1)
      | ~ m1_subset_1(X4,sK0) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (27008)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (27014)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (27008)Refutation not found, incomplete strategy% (27008)------------------------------
% 0.21/0.47  % (27008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27026)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (27008)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (27008)Memory used [KB]: 10618
% 0.21/0.48  % (27008)Time elapsed: 0.051 s
% 0.21/0.48  % (27008)------------------------------
% 0.21/0.48  % (27008)------------------------------
% 0.21/0.48  % (27022)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (27021)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (27009)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (27013)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (27020)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (27016)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (27010)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (27010)Refutation not found, incomplete strategy% (27010)------------------------------
% 0.21/0.50  % (27010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27010)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (27010)Memory used [KB]: 10618
% 0.21/0.50  % (27010)Time elapsed: 0.084 s
% 0.21/0.50  % (27010)------------------------------
% 0.21/0.50  % (27010)------------------------------
% 0.21/0.50  % (27026)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f1400,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f236,f720,f1128,f1384,f1399])).
% 0.21/0.50  fof(f1399,plain,(
% 0.21/0.50    spl7_7 | spl7_10 | ~spl7_22),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1398])).
% 0.21/0.50  fof(f1398,plain,(
% 0.21/0.50    $false | (spl7_7 | spl7_10 | ~spl7_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f1397,f161])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    ~v1_xboole_0(sK1) | spl7_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f159])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    spl7_7 <=> v1_xboole_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.50  fof(f1397,plain,(
% 0.21/0.50    v1_xboole_0(sK1) | (spl7_10 | ~spl7_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f1390,f235])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    ~m1_subset_1(sK5(sK3),sK1) | spl7_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f233])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    spl7_10 <=> m1_subset_1(sK5(sK3),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.50  fof(f1390,plain,(
% 0.21/0.50    m1_subset_1(sK5(sK3),sK1) | v1_xboole_0(sK1) | ~spl7_22),
% 0.21/0.50    inference(resolution,[],[f728,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.50  fof(f728,plain,(
% 0.21/0.50    r2_hidden(sK5(sK3),sK1) | ~spl7_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f727])).
% 0.21/0.50  fof(f727,plain,(
% 0.21/0.50    spl7_22 <=> r2_hidden(sK5(sK3),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.50  fof(f1384,plain,(
% 0.21/0.50    spl7_22),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1379])).
% 0.21/0.50  fof(f1379,plain,(
% 0.21/0.50    $false | spl7_22),
% 0.21/0.50    inference(resolution,[],[f1374,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    r2_hidden(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.50    inference(resolution,[],[f96,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X4] : (! [X5] : (k4_tarski(X4,X5) != sK3 | ~m1_subset_1(X5,sK1)) | ~m1_subset_1(X4,sK0)) & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) & r2_hidden(sK3,sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (! [X4] : (! [X5] : (k4_tarski(X4,X5) != X3 | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2)) => (! [X4] : (! [X5] : (k4_tarski(X4,X5) != sK3 | ~m1_subset_1(X5,sK1)) | ~m1_subset_1(X4,sK0)) & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) & r2_hidden(sK3,sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (! [X4] : (! [X5] : (k4_tarski(X4,X5) != X3 | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ~(! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => k4_tarski(X4,X5) != X3)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ~(! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => k4_tarski(X4,X5) != X3)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_subset_1)).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(sK2,X0) | r2_hidden(sK3,X0)) )),
% 0.21/0.50    inference(resolution,[],[f65,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_tarski(sK3),X0) | ~r1_tarski(sK2,X0)) )),
% 0.21/0.50    inference(resolution,[],[f43,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    r1_tarski(k1_tarski(sK3),sK2)),
% 0.21/0.50    inference(resolution,[],[f26,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    r2_hidden(sK3,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f1374,plain,(
% 0.21/0.50    ( ! [X3] : (~r2_hidden(sK3,k2_zfmisc_1(X3,sK1))) ) | spl7_22),
% 0.21/0.50    inference(superposition,[],[f755,f120])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    sK3 = k4_tarski(sK4(sK3),sK5(sK3))),
% 0.21/0.50    inference(resolution,[],[f100,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_tarski(sK4(X0),sK5(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k4_tarski(sK4(X0),sK5(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f10,f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK4(X0),sK5(X0)) = X0)),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.21/0.50  fof(f755,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,sK5(sK3)),k2_zfmisc_1(X3,sK1))) ) | spl7_22),
% 0.21/0.50    inference(resolution,[],[f729,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.50    inference(nnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.50  fof(f729,plain,(
% 0.21/0.50    ~r2_hidden(sK5(sK3),sK1) | spl7_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f727])).
% 0.21/0.50  fof(f1128,plain,(
% 0.21/0.50    ~spl7_7),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1120])).
% 0.21/0.50  fof(f1120,plain,(
% 0.21/0.50    $false | ~spl7_7),
% 0.21/0.50    inference(resolution,[],[f1107,f100])).
% 0.21/0.50  fof(f1107,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,sK1))) ) | ~spl7_7),
% 0.21/0.50    inference(condensation,[],[f1105])).
% 0.21/0.50  fof(f1105,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,sK1)) | ~r2_hidden(X0,k2_zfmisc_1(X2,X3))) ) | ~spl7_7),
% 0.21/0.50    inference(superposition,[],[f902,f29])).
% 0.21/0.50  fof(f902,plain,(
% 0.21/0.50    ( ! [X6,X7,X5] : (~r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,sK1))) ) | ~spl7_7),
% 0.21/0.50    inference(resolution,[],[f895,f31])).
% 0.21/0.50  fof(f895,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl7_7),
% 0.21/0.50    inference(resolution,[],[f160,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(rectify,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    v1_xboole_0(sK1) | ~spl7_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f159])).
% 0.21/0.50  fof(f720,plain,(
% 0.21/0.50    spl7_9),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f715])).
% 0.21/0.50  fof(f715,plain,(
% 0.21/0.50    $false | spl7_9),
% 0.21/0.50    inference(resolution,[],[f709,f100])).
% 0.21/0.50  fof(f709,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK3,k2_zfmisc_1(sK0,X0))) ) | spl7_9),
% 0.21/0.50    inference(superposition,[],[f257,f120])).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK4(sK3),X0),k2_zfmisc_1(sK0,X1))) ) | spl7_9),
% 0.21/0.50    inference(resolution,[],[f241,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    ~r2_hidden(sK4(sK3),sK0) | spl7_9),
% 0.21/0.50    inference(subsumption_resolution,[],[f239,f40])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    ~r2_hidden(sK4(sK3),sK0) | v1_xboole_0(sK0) | spl7_9),
% 0.21/0.50    inference(resolution,[],[f231,f34])).
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    ~m1_subset_1(sK4(sK3),sK0) | spl7_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f229])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    spl7_9 <=> m1_subset_1(sK4(sK3),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    ~spl7_9 | ~spl7_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f227,f233,f229])).
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    ~m1_subset_1(sK5(sK3),sK1) | ~m1_subset_1(sK4(sK3),sK0)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f223])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    sK3 != sK3 | ~m1_subset_1(sK5(sK3),sK1) | ~m1_subset_1(sK4(sK3),sK0)),
% 0.21/0.50    inference(superposition,[],[f28,f120])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK3 | ~m1_subset_1(X5,sK1) | ~m1_subset_1(X4,sK0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (27026)------------------------------
% 0.21/0.50  % (27026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27026)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (27026)Memory used [KB]: 6652
% 0.21/0.50  % (27026)Time elapsed: 0.080 s
% 0.21/0.50  % (27026)------------------------------
% 0.21/0.50  % (27026)------------------------------
% 0.21/0.50  % (27006)Success in time 0.144 s
%------------------------------------------------------------------------------
